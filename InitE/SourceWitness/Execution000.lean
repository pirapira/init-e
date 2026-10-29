import Tools.SourceCheckpoint
import InitE.SourceWitness.Entry
import InitE.SourceWitness.Input

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceAtomicReduction InitE.SourceSupportReduction Tools.SourceCheckpoint InitE.SourceContextReduction
  InitE.SourceLookupReduction InitE.SourceMemoryReduction InitE.SourceReduction
  InitE.NameComputation InitE.SourceWitness

namespace InitE.SourceWitness

-- A proposed clock bound; the eventual terminal-state certificate must check it.
source_checkpoint execution000 := execution input 32000 budget 500

end InitE.SourceWitness
