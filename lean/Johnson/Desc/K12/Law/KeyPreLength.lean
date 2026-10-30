-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsKeyChains
/-
Johnson/Desc/K12/Law/KeyPreLength.lean: HOW MANY BLOCKS STAND IN FRONT OF EACH PROXIMITY TEST IN THE KEY
FILE's THREE FLAT LISTS: so that a statement that names a test's entry BY ITS CUT (keyFirst_cut ·
keyShared_cut(_omega) · keySecond_cut: Johnson/Desc/K12/Law/SitsKeyChains.lean) and one that names it BY
ITS NUMBER IN THE LIST (rng_at | U_at | O_at | own_at:
Johnson/RunOne/Law/K12AtField.lean) speak of one entry. The right sides are written as that file
writes its numbers; the abbreviation tableBlocks X P (K12SeatsAt.lean, beside it) is
Desc.K14.blocksOr (Key.sharedPar X.chains (Key.beforeSharedPoint P)), written out here: no file
under Johnson/RunOne/ is imported. FACTS ON THE PLAN. NO SOUNDNESS IS CLAIMED.
NOTHING ON HIDING.
  lookupLink_length    a lookup's link lays six blocks
  keyFirstPre_length   (keyFirstPre one D told set N).length = 2 + 6 * (Key.lookupsOf one).length + 1
  keySharedPre_length  (keySharedPre c P).length = 1 + ((Desc.K14.blocksOr …).length + 0)
  keySharedPreGu_length (keySharedPre c P ++ [keyGu P]).length = 1 + ((Desc.K14.blocksOr …).length + 1)
  secondPre_length     (secondPre Cl' p K).length = 2: at both files' last chains
NO PREMISE. How many blocks Desc.K14.blocksOr lays (eight, where the chain passes its test on the plan)
is the shared chain's files' to say.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem lookupLink_length (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : Nat)
    (x : Key.Lookup) : (Key.lookupLink one set i x).blocksInOrder.length = 6 := rfl


theorem keyFirstPre_length (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) :
    (keyFirstPre one D told set N).length = 2 + 6 * (Key.lookupsOf one).length + 1 := by
  have hl : ∀ l : List (Key.Lookup × Nat),
      ((l.map fun x => Key.lookupLink one set x.2 x.1).flatMap Link.blocksInOrder).length = 6 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatMap_cons, List.length_append, ih, lookupLink_length,
        List.length_cons]
      omega
  have h := hl (Key.lookupsOf one).zipIdx
  rw [List.length_zipIdx] at h
  show ((Key.firstChain one D told set N).first.asBare ::
      (Key.firstChain one D told set N).front.map Block.asBare ++
      (((Key.lookupsOf one).zipIdx.map fun x => Key.lookupLink one set x.2 x.1).flatMap Link.blocksInOrder) ++
      [(Key.layRows one).asBare]).length = _
  rw [List.length_append, List.length_append, h]
  show (1 + 1) + 6 * (Key.lookupsOf one).length + 1 = _
  rfl


theorem keySharedPre_length (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    (keySharedPre c P).length =
      1 + ((_root_.Desc.K14.blocksOr (Key.sharedPar c (Key.beforeSharedPoint P))).length + 0) := by
  unfold keySharedPre
  rw [List.length_cons, List.length_map]
  omega


theorem keySharedPreGu_length (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    (keySharedPre c P ++ [keyGu P]).length =
      1 + ((_root_.Desc.K14.blocksOr (Key.sharedPar c (Key.beforeSharedPoint P))).length + 1) := by
  rw [List.length_append, keySharedPre_length]
  rfl

/-- At both files' last chains. -/
theorem secondPre_length (Cl' : Type) (p : Third.P₁₄) (K : Blk') :
    (secondPre Cl' p K).length = 2 := rfl

end H2K.JointK

#print axioms H2K.JointK.lookupLink_length
#print axioms H2K.JointK.keyFirstPre_length
#print axioms H2K.JointK.keySharedPre_length
#print axioms H2K.JointK.keySharedPreGu_length
#print axioms H2K.JointK.secondPre_length
