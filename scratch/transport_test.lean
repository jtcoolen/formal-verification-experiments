import Merkle.Signature
import Merkle.Free

open Merkle Merkle.Free

namespace Test

example [m : MerkleHash Nat (Dig Nat)] : (merkleSigOf m).leaf = m.leaf := rfl

example [m : MerkleHash Nat (Dig Nat)] : Sig.leaf (s := merkleSigOf m) 0 = m.leaf 0 := rfl

example [m : MerkleHash Nat (Dig Nat)] : (merkleSigOf m).node = m.node := rfl

end Test