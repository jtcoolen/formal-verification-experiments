import Merkle.Basic
import Merkle.Proof
import Merkle.Free
import Merkle.Complexity
import Merkle.Signature
import Merkle.Security
import Merkle.Usage
import Merkle.Sha3
import Merkle.Sha3.Examples
import Merkle.Regression

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
  rehash, `n` to address or fold an available proof, and the uncached proof-generation cost),
  with the separation theorem `not_pow_isBigO_linear`.
* `Merkle.Signature` - the same construction split along the axiom seam: `MerkleSig` carries
  only the hash functions, `SigCollisionFree` the assumptions. `Sig.complete` and `Sig.update`
  hold for *any* signature, so a real hash like SHA3 can be installed and used without assuming
  anything.
* `Merkle.Security` - security bounds: the constructive collision extractor
  `collision_of_rootHash_eq`, the exact forgery count `accepting_value_unique`, and the
  information-theoretic barrier `digest_cannot_be_small`.
* `Merkle.Sha3` - real SHA3-512 (via lean4-hash) installed as a signature: correctness holds
  without assumptions about the hash, and the file proves why absolute injectivity cannot be
  assumed there.
* `Merkle.Sha3.Examples` - worked applications over SHA3-512: key-value commitments, sparse
  subtrees, a 16-entry authenticated log snapshot, batch writes, multi-inclusion certificates,
  and binding and false-inclusion reductions without injectivity assumptions.
* `Merkle.Regression` - checked witnesses for colliding finite signatures, numeric addressing,
  and depth-zero cost accounting.
* `Merkle.Usage` - worked applications: building trees from flat vectors, sparse subtrees,
  batch updates, authenticated log snapshots, multi-inclusion certificates, and checked examples.
-/
