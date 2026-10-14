import Merkle.Basic
import Merkle.Proof
import Merkle.Free
import Merkle.Complexity
import Merkle.Security
import Merkle.Usage

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
* `Merkle.Free` - the free hash algebra `Dig`, the concrete model that makes every theorem
  above non-vacuous, with both axioms proved by constructor injectivity.
* `Merkle.Complexity` - exact closed-form costs of every operation (`2 ^ (n+1) - 1` hashes to
  rehash, `n` to address, verify or update) and the separation theorem `not_pow_isBigO_linear`.
* `Merkle.Security` - security bounds: the constructive collision extractor
  `collision_of_rootHash_eq`, the exact forgery count `accepting_value_unique`, and the
  information-theoretic barrier `digest_cannot_be_small`.
* `Merkle.Usage` - worked applications: building trees from flat vectors, sparse subtrees,
  batch updates, append-only logs, multi-inclusion certificates, and checked examples.
-/
