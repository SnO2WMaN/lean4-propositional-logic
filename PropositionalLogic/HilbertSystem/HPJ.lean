import PropositionalLogic.Notations
import PropositionalLogic.HilbertSystem.Definitions
import PropositionalLogic.HilbertSystem.HPM₀
import PropositionalLogic.HilbertSystem.HPM

namespace PropositionalLogic.HilbertSystem

open Finset Notations HilbertSystem

class HPJ
  (L : Type u) [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  extends HPM L, HasEFQ L

namespace HPJ

variable
  {L : Type u} [DecidableEq L] [HilbertSystem L]
  [HasBot L] [HasArrow L] [HasLnot L] [HasLor L] [HasLand L] [HasLiff L]
  [HPJ L]

open HilbertSystem
open HPM₀ HPM

section Extended

open HasCM₂ in
instance [HasCM₂ L] : HasDNE L where
  axiomDNE Γ φ := by
    admit

end Extended

end HPJ

end PropositionalLogic.HilbertSystem
