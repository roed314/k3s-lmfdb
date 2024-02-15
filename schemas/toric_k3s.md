Name: `toric_k3s`

| Column | Type | Description |
|---|---|--- |
| label | text |family label |
| KS_num | integer | index in Kreuzer-Skarke database for reflexive; null if not reflexive |
| Reid_num | integer | index in Reid database for weighted projective space (wps); null if not wps |
| vertices | integer[][] | list of vertices |
| toric_lattice | text | label for the lattice consiting of pullbacks of toric divisors (includes exceptional divisors coming from resolution of sinularities on the ambient space) |
| corrected_lattice | text | label for the corrected lattice of pullback of toric divisors (contains toric_lattice, maybe only defined for reflexive) |
| toric_rank | integer | rank of toric_lattice |
| corrected_rank | integer | rank of toric_lattice |
| delta | integer | rho_cor - rho_tor |
| mirror_label | text | label of the mirror family |
| ambient_is_reflexive | boolean | is the polytope reflexive |
| ambient_is_maximal | boolean | is the polytope maximal |
| wps_weights | integer[] | list of weights if wps |
| equivalent_families | text[] | list of other toric families that are birationally equivalent over C |