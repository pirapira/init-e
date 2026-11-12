#!/usr/bin/env python3
"""Generate GuestBound/SepFrameOps.lean: for every function called by
`op_dispatch` whose body is built only from the steps that have a rule in
`SepFrameOp.lean`, a proof that it satisfies `HandlerQ` under the frame
invariant. Run from the repository root."""
import re

SRC = open('Guest/SoftwareAst.lean').read()


def names():
    tail = SRC[SRC.rindex('def guestAst'):]
    items = re.findall(r'guest[A-Z][a-z]+_\w+', tail)
    return [(i, it[len('guestFn_'):]) for i, it in enumerate(items) if it.startswith('guestFn_')]


def body_text(name):
    i = SRC.index('{ name := "%s"' % name)
    k = SRC.index('(', SRC.index('body :=', i))
    d = 0
    for q in range(k, len(SRC)):
        if SRC[q] == '(':
            d += 1
        elif SRC[q] == ')':
            d -= 1
            if d == 0:
                return re.sub(r'\s+', ' ', SRC[k:q + 1])


TOK = re.compile(r'\s*("(?:[^"\\]|\\.)*"|[()\[\],]|[^\s()\[\],]+)')


class Node(list):
    """A parsed application / list / tuple, remembering its source text."""
    text = ''


def parse(text):
    toks = [(m.group(1), m.start(1), m.end(1)) for m in TOK.finditer(text)]
    pos = 0

    def expr():
        nonlocal pos
        tok, a, _ = toks[pos]
        if tok == '(':
            pos += 1
            items, tuple_ = [], False
            while toks[pos][0] != ')':
                if toks[pos][0] == ',':
                    tuple_ = True
                    pos += 1
                else:
                    items.append(expr())
            b = toks[pos][2]
            pos += 1
            if len(items) == 1 and not tuple_:
                return items[0]
            n = Node((['TUPLE'] if tuple_ else []) + items)
            n.text = text[a:b]
            return n
        if tok == '[':
            pos += 1
            items = []
            while toks[pos][0] != ']':
                if toks[pos][0] == ',':
                    pos += 1
                else:
                    items.append(expr())
            b = toks[pos][2]
            pos += 1
            n = Node(['LIST'] + items)
            n.text = text[a:b]
            return n
        pos += 1
        return tok

    def app():
        nonlocal pos
        items = []
        while pos < len(toks) and toks[pos][0] not in (')', ']', ','):
            items.append(expr())
        return items[0] if len(items) == 1 else Node(items)

    # A parenthesised term is an application of its head to its arguments.
    def top():
        return expr()

    return top()


def txt(n):
    return n.text if isinstance(n, Node) else n


ALL = {}
IDX = {}
for i, n in names():
    ALL[n] = body_text(n)
    IDX[n] = i


def pure(f, seen=None):
    seen = seen or set()
    if f in seen:
        return True
    seen.add(f)
    b = ALL[f]
    if re.search(r'Prog\.store|Prog\.assign VarKind\.global|shMem|extCall|Prog\.raise|some \("', b):
        return False
    return all(pure(c, seen) for c in set(re.findall(r'"(\w+)"', b)) if c in ALL and c != f)


def pure_e(f, seen=None):
    """Like `pure`, but `raise EvmErr` is allowed."""
    seen = seen or set()
    if f in seen:
        return True
    seen.add(f)
    b = ALL[f].replace('Prog.raise "EvmErr"', '')
    if re.search(r'Prog\.store|Prog\.assign VarKind\.global|shMem|extCall|Prog\.raise|some \("', b):
        return False
    return all(pure_e(c, seen) for c in set(re.findall(r'"(\w+)"', b)) if c in ALL and c != f)


def checks(f, raises):
    """The two checker facts about a callee, as Lean terms."""
    return [
        f'(keepFn_sound (quietKeeper E) hE.functions {DEPTH} "{f}"',
        f'    (show keepFn quietLeaf Guest.Software.guestAst {DEPTH} "{f}" = true by decide +kernel))',
        f'  (raiseFn_sound _ hE.functions {DEPTH} "{f}"',
        f'    (show raiseFn ({raises}) Guest.Software.guestAst {DEPTH} "{f}" = true by',
        f'      decide +kernel))',
    ]


PC_ADDR = '(Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 0))])'
DEPTH = 6
COMB4 = ['Shape.comb', ['LIST', 'Shape.one', 'Shape.one', 'Shape.one', 'Shape.one']]
NOINFO = ['some', ['TUPLE', 'none', 'none']]


def const(n):
    """The literal of `Exp.const (BitVec.ofNat 64 k)`, or None."""
    if isinstance(n, list) and len(n) == 2 and n[0] == 'Exp.const' and \
            isinstance(n[1], list) and n[1][:2] == ['BitVec.ofNat', '64']:
        return n[1][2]
    return None


class Unsupported(Exception):
    pass


def bullet(lines):
    return ['· ' + lines[0]] + ['  ' + l for l in lines[1:]]


def shape_of(sh):
    if isinstance(sh, list) and list(sh) == COMB4:
        return 'four'
    if sh == 'Shape.one':
        return 'one'
    return None


LOOKUP = 'by simp (config := { decide := true }) [update_lookup]'


def gen(node, hq, shapes, spent):
    """Tactic lines proving the statement `node` under the frame invariant.
    `hq` is the term showing that the current postcondition accepts a handler
    outcome; `shapes` maps locals to a known shape; `spent` says whether gas
    has been charged."""
    head = node[0] if isinstance(node, list) else node
    if head == 'Prog.return':
        if const(node[1]) != '0' or not spent:
            raise Unsupported('return')
        return [f'exact op_return hok hp (by decide) h {hq}']
    if head == 'Prog.raise':
        if node[1] != '"EvmErr"' or const(node[2]) is None:
            raise Unsupported('raise')
        return [f'exact op_raise hok hp h {hq}.abort']
    if head == 'Prog.dec':
        x, init = node[1].strip('"'), node[3]
        if isinstance(init, list) and init[0] == 'Exp.load' and list(init[1]) == COMB4:
            return [f'refine op_dec_ev h (fun _ hev_{x} h => ?_)',
                    f'have hval_{x} := arg4_load hE _ _ hev_{x}'] + \
                gen(node[4], hq + '.restore', dict(shapes, **{x: 'fourval'}), spent)
        return ['refine op_dec h (fun _ h => ?_)'] + \
            gen(node[4], hq + '.restore', dict(shapes, **{x: None}), spent)
    if head == 'Prog.decCall':
        x, sh, f, args, rest = node[1].strip('"'), node[2], node[3].strip('"'), node[4], node[5]
        inner = dict(shapes, **{x: shape_of(sh)})
        if f == 'stack_pop':
            return [f'refine op_pop_sh hE hok hp h {hq}.abort (fun _ g m hsh_{x} hok hp h => ?_)'] + \
                gen(rest, hq + '.restore', inner, spent)
        if f in ALL and pure(f):
            return [
                f'refine op_quiet (keepFn_sound (quietKeeper E) hE.functions {DEPTH} "{f}"',
                f'    (show keepFn quietLeaf Guest.Software.guestAst {DEPTH} "{f}" = true by decide +kernel))',
                f'  (raiseFn_sound _ hE.functions {DEPTH} "{f}"',
                f'    (show raiseFn (fun _ => false) Guest.Software.guestAst {DEPTH} "{f}" = true by',
                f'      decide +kernel))',
                f'  h {hq}.abort (fun _ hsh_{x} h => ?_)',
            ] + gen(rest, hq + '.restore', inner, spent)
        if f in ALL and pure_e(f):
            c = checks(f, 'fun x => x == "EvmErr"')
            return ['refine op_quiet_raise ' + c[0]] + c[1:] + \
                [f'  hok hp h {hq}.abort (fun _ hsh_{x} h => ?_)'] + \
                gen(rest, hq + '.restore', inner, spent)
        raise Unsupported('decCall ' + f)
    if head == 'Prog.seq':
        first, rest = node[1], node[2]
        if isinstance(first, list) and first[0] == 'Prog.ite' and first[3] == 'Prog.skip':
            # `if c { P }` where P ends the handler; otherwise continue with `rest`.
            then = gen(first[2], hq + '.mid', shapes, spent)
            return (['refine WPr.seq_ite_skip ?_ ?_'] + bullet(then)
                    + bullet(gen(rest, hq, shapes, spent)))
        if isinstance(first, list) and first[0] == 'Prog.store' and txt(first[1]) == PC_ADDR:
            v = first[2]
            if isinstance(v, list) and v[0] == 'Exp.rField' and isinstance(v[2], list) and \
                    v[2][:2] == ['Exp.var', 'VarKind.local'] and \
                    shapes.get(v[2][2].strip('"')) == 'four':
                x = v[2][2].strip('"')
                return [f'refine op_set_pc hE (arg1_rfield4 {v[1]} (by decide) ({LOOKUP}) hsh_{x})',
                        '  hok hp h (fun _ m hok hp h => ?_)'] + gen(rest, hq, shapes, spent)
            raise Unsupported('store to pc')
        if not (isinstance(first, list) and first[0] == 'Prog.call' and list(first[1]) == NOINFO):
            raise Unsupported('seq ' + str(first)[:40])
        f, args = first[2].strip('"'), first[3]
        if f == 'charge_gas' and const(args[1]) is not None:
            g = const(args[1])
            return [f'refine op_charge hE {g}#64 hok hp h {hq}.abort (fun g m hok hp h => ?_)'] + \
                gen(rest, hq, shapes, spent or int(g) > 0)
        if f == 'pc_add' and const(args[1]) is not None:
            return [f'refine op_pc_add hE (d := {const(args[1])}#64)',
                    '  (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h',
                    f'  {hq}.abort (fun g m hok hp h => ?_)'] + gen(rest, hq, shapes, spent)
        a = args[1] if len(args) > 1 else None
        islocal = isinstance(a, list) and a[:2] == ['Exp.var', 'VarKind.local']
        if f == 'stack_push':
            if isinstance(a, list) and a[0] == 'Exp.load' and list(a[1]) == COMB4:
                hc = 'stack_push_any_hc hE (arg4_load hE _) e _ _ _ _ fv hok.ok'
            elif islocal and shapes.get(a[2].strip('"')) == 'four':
                v = a[2].strip('"')
                hc = f'stack_push_any_hc hE (arg4_shape ({LOOKUP}) hsh_{v}) e _ _ _ _ fv hok.ok'
            elif islocal and shapes.get(a[2].strip('"')) == 'fourval':
                v = a[2].strip('"')
                hc = f'stack_push_any_hc hE (arg4_ex ({LOOKUP}) hval_{v}) e _ _ _ _ fv hok.ok'
            elif isinstance(a, list) and a[0] == 'Exp.rStruct' and len(a[1]) == 5 and \
                    all(isinstance(x, list) and x[0] == 'Exp.op' for x in a[1][1:]):
                hc = 'stack_push_any_hc hE (arg4_ops hE _ _ _ _ _ _ _ _) e _ _ _ _ fv hok.ok'
            else:
                raise Unsupported('stack_push argument')
        elif f == 'stack_push_word':
            if isinstance(a, list) and a[:2] == ['Exp.load', 'Shape.one']:
                hc = 'stack_push_word_hc hE _ e _ _ _ _ fv hok.ok'
            elif islocal and shapes.get(a[2].strip('"')) == 'one':
                v = a[2].strip('"')
                hc = (f'stack_push_word_any_hc hE (arg1_shape ({LOOKUP}) hsh_{v}) '
                      'e _ _ _ _ fv hok.ok')
            else:
                raise Unsupported('stack_push_word argument')
        elif f == 'stack_push_bool':
            hc = ('fun p b _ cl hlk _ _ => stack_push_bool_framed hE p b hlk '
                  '⟨cl, _, _, _⟩ e _ _ _ _ fv hok.ok')
        elif f in ALL and pure_e(f):
            c = checks(f, 'fun x => x == "EvmErr"')
            return ['refine op_call_raise ' + c[0]] + c[1:] + \
                [f'  hok hp h {hq}.abort ?_'] + gen(rest, hq, shapes, spent)
        else:
            raise Unsupported('call ' + f)
        return [f'refine op_push hok hp h {hq}.abort', f'  ({hc})',
                '  (fun _ g m hok hp h => ?_)'] + gen(rest, hq, shapes, spent)
    raise Unsupported(str(head))


out = ['''import InitECandidate.Solver.GuestBound.SepFrameOp2

/-!
# Stack handlers under the frame invariant

Generated by `tools/gen-frame-ops.py`. Each handler here either aborts (a trap,
or `EvmErr` with the frame invariant intact and no gas gained) or returns 0
with the frame invariant intact and strictly less gas left.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}
''']
handlers = sorted(set(re.findall(r'"(op_\w+)"', ALL['op_dispatch'])), key=lambda n: IDX[n])
done, skipped = [], []
for n in handlers:
    try:
        lines = gen(parse(ALL[n]), 'AcceptsH.refl', {}, False)
    except Unsupported as u:
        skipped.append((n, str(u)))
        continue
    done.append(n)
    script = '\n'.join('  ' + l for l in lines)
    out.append(f'''
theorem «{n}_frame» (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "{n}" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s body (HandlerQ M K e fv R s.ffi X0) := by
  have hbody := (fun_of_index {IDX[n]} hE.functions (by guest_decl_at {IDX[n]})
    (by decide +kernel) hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
{script}
''')
out.append('\nend InitECandidate.Solver.GuestBound\n')
open('submission/InitECandidate/Solver/GuestBound/SepFrameOps.lean', 'w').write(''.join(out))
print(len(done), 'handlers:', ' '.join(done))
print(len(skipped), 'skipped')
import collections
for why, k in collections.Counter(w for _, w in skipped).most_common(12):
    print('  ', k, why)
