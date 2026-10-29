import InitE.SourceWitness.Execution000
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceAtomicReduction InitE.SourceSupportReduction Tools.SourceCheckpoint InitE.SourceContextReduction
  InitE.SourceLookupReduction InitE.SourceMemoryReduction InitE.SourceReduction
  InitE.NameComputation InitE.SourceWitness
namespace InitE.SourceWitness
source_checkpoint execution001 := execution000 budget 500
end InitE.SourceWitness
