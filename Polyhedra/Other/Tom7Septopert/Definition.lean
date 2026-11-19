import Definitions.Polyhedra

/-!
# The septopert of Tom 7

The polyhedron `Other.Tom7Septopert.polyhedron`: the convex hull of 7 points.
-/

namespace Nieuwland.Other.Tom7Septopert

open Classical in
/-- The septopert of Tom 7: the convex hull of these 7 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![-470319/524288, 327651/1048576, 327651/1048576],
    ![327651/1048576, -470319/524288, 327651/1048576],
    ![327651/1048576, 327651/1048576, -470319/524288],
    ![21999/32768, 11947/262144, 11947/262144],
    ![11947/262144, 21999/32768, 11947/262144],
    ![11947/262144, 11947/262144, 21999/32768],
    ![-514207/1048576, -514207/1048576, -514207/1048576]].toFinset

end Nieuwland.Other.Tom7Septopert
