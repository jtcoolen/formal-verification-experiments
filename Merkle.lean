import Merkle.Basic
import Merkle.Proof
import Merkle.Examples

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

/-!
The root module of the `Merkle` library. Import this to get everything:

* `Merkle.Basic` - indexed perfect trees, indexed paths, the `MerkleHash` algebra, and
  `rootHash_injective` (collision resistance of the root digest).
* `Merkle.Proof` - authentication paths, `verify`, `verify_complete`, `verify_sound`
  (the no-forgery theorem), and `rootHash_update` (incremental update correctness).
* `Merkle.Examples` - a fully proved instantiation of the algebra, and the counting barrier
  that no compressing hash can overcome.
-/

