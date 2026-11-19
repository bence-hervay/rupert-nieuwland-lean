import Polyhedra.Other.CornerTetrahedron.Proof.Points
import Modules.Check.Leaf.FullDim
import Polyhedra.Other.CornerTetrahedron.Certificates.Weak
import Polyhedra.Other.CornerTetrahedron.Certificates.Diameter

set_option linter.style.longLine false

/-!
# The fixture `other/corner-tetrahedron`: an exact Nieuwland number from the diameter bound

The exact certificate `gs://main-69696-data/noperts-results/nieuwland-exact-2026-11-16-other/corner-tetrahedron/exact.jsonl`, exported by `code/lean-export scaled --fit`: one record for every pose, a diameter cover at the exact scale `Θ` (`Lift.cover_ok`: scaled by `Θ`, the solid does not fit through itself in any pose, `Check.Diam.Cover.not_fitsThrough`), and a weak fit at `Θ` (`Lift.weak_check`). The Nieuwland number of `Other.CornerTetrahedron.polyhedron` is `Θ`.
-/

namespace Nieuwland.Polyhedra

open Check

/-- **The fixture `other/corner-tetrahedron`: the Nieuwland number.** From the diameter cover and the weak fit at the exact scale `Θ` (`Check.Polyhedron.nieuwland_eq_of_diameter_lift`), with `Θ` as a real number (`Lift.Theta_re`). -/
theorem otherCornerTetrahedron_nieuwland : Other.CornerTetrahedron.polyhedron.nieuwland = realRoot [-4/3, 0, 1] 0 4 := by
  have hdim : Other.CornerTetrahedron.polyhedron.FullDim := by
    rw [Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.eq_smul]
    exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.span_ok).smul (by norm_num)
  rw [← Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.Lift.Theta_re]
  exact Check.Polyhedron.nieuwland_eq_of_diameter_lift (c := 1) one_ne_zero (by rw [Nieuwland.Polyhedron.smul_one]; exact Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.Lift.points_eq) Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.Lift.cover_ok Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.Lift.weak_check rfl rfl Nieuwland.Certs.NieuwlandOtherCornerTetrahedron.eq_smul (by norm_num) hdim

end Nieuwland.Polyhedra
