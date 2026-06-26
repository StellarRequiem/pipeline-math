-- Frozen interface for the Problem 30(c) counterexample: the definitions
-- (`Defs`) and the immutable theorem statements (`Theorems`), plus the
-- `Proofs/` stage modules that discharge them, and the `Discharge`/`Solution`
-- gates. See `PROGRESS.md` and `BLUEPRINT.md`.
import Prob30c.Defs
import Prob30c.Theorems
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.RingModel.Basic
import Prob30c.Proofs.Cancellation.Basic
import Prob30c.Proofs.LowerA.Basic
import Prob30c.Proofs.UpperA.Basic
import Prob30c.Proofs.PolyCancel.Basic
import Prob30c.Proofs.LowerAX.Basic
import Prob30c.Proofs.UpperAX.Basic
import Prob30c.Proofs.Wrap.Basic
import Prob30c.Discharge
import Prob30c.Solution
