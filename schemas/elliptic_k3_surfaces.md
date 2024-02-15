Table name: `elliptic_k3_surfaces`

| Column |Type | Description |
| ---- | ---- | ---- |
| label | text | label of the surface |
| K3_family | text | label of the K3 family |
| polarized_lattice | text | label of the positive definite lattice L |
| mw_rank | smallint | rank of the Mordell-Weil group |
| mw_torsion | smallint[] | elementary divisors of the torsion of Mordell-Weil |
| reducible_fibers | text[] | a description of the reducible fibers, by name of the ADE lattices|
| multiplicity | integer | number of inequivalent fibrations with the same lattice |
| mw_pairing |text | label of the quadratic form on Mordel-Weil, scaled to be integral|
| mw_denom | integer | scaling factor for mw_pairing |