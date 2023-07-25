import PropositionalLogic.Notation
import PropositionalLogic.HilbertSystem
import PropositionalLogic.HPM₀
import PropositionalLogic.HPM

namespace PropositionalLogic

open Finset Notation HilbertSystem

class HPJ
  (L : Type u) [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L]
  extends HasEFQ L

namespace HPJ

variable
  {L : Type u} [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L]
  [HPJ L]

open HilbertSystem
open HPM₀ HPM

end HPJ

end PropositionalLogic
