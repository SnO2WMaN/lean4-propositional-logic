import PropositionalLogic.HilbertSystem
import PropositionalLogic.HPM₀
import PropositionalLogic.HPM

namespace PropositionalLogic

open Finset Notation HilbertSystem

class HPK
  (L : Type u) [DecidableEq L] [HilbertSystem L]
 [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
 extends HPM L, HasDNE L

namespace HPK

variable
  {L : Type u} [DecidableEq L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  [HilbertSystem L] [HPK L]

open HilbertSystem HPM₀ HPM

end HPK

end PropositionalLogic
