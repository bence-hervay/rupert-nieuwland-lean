import Polyhedra.Archimedean.TruncatedIcosidodecahedron.Definition
import Polyhedra.Archimedean.TruncatedIcosidodecahedron.Certificates.Shared

set_option linter.style.longLine false

/-!
# The truncated icosidodecahedron: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandArchimedeanTruncatedIcosidodecahedron

open Check Cert

theorem eq_smul : Archimedean.TruncatedIcosidodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54, pt55, pt56,
    pt57, pt58, pt59, pt60, pt61, pt62, pt63, pt64, pt65, pt66, pt67, pt68, pt69, pt70, pt71, pt72,
    pt73, pt74, pt75, pt76, pt77, pt78, pt79, pt80, pt81, pt82, pt83, pt84, pt85, pt86, pt87, pt88,
    pt89, pt90, pt91, pt92, pt93, pt94, pt95, pt96, pt97, pt98, pt99, pt100, pt101, pt102, pt103,
    pt104, pt105, pt106, pt107, pt108, pt109, pt110, pt111, pt112, pt113, pt114, pt115, pt116,
    pt117, pt118, pt119]

end Nieuwland.Certs.NieuwlandArchimedeanTruncatedIcosidodecahedron
