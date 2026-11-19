import Polyhedra.Other.Tom7Candidate231Ideal.Definition
import Polyhedra.Other.Tom7Candidate231Ideal.Certificates.Shared

set_option linter.style.longLine false

/-!
# The candidate 231 of Tom 7 (ideal coordinates): the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Results.Gen.ExternalTom7Candidate231Ideal

open Check Cert

theorem eq_smul : Other.Tom7Candidate231Ideal.polyhedron = (Polyhedron.ofPoints points).smul (1 / 5862196751232270670763990755657937424866701692419942715923480041777338282026605759126760636670790169613455646643458534423367468496956993687129681230678019815035190161509855124264191409268981760) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Other.Tom7Candidate231Ideal.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19]

end Nieuwland.Results.Gen.ExternalTom7Candidate231Ideal
