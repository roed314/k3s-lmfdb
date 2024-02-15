Table name: `k3_surface_models`

| Column |Type | Description |
| --- | --- | --- |
| K3_family| text | label of the K3 family |
| elliptic_surface| text | label of the elliptic surface |
| ambient_space | text | label of the ambient toric variety |
| model_type | smallint | type of model - projective, toric, complete intersection|
| singularity_types | text[] | types of singularities |
| dont_display | boolean | true if we want to display on page |
| equation | text[] | equations defining the model as text to be displayed|
| degrees | integer[] | list of lists of degrees |