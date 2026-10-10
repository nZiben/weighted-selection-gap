import Lake
open Lake DSL

package «weighted-selection-scalar» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib Scalar
