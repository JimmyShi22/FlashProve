-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/KLive.lean: K10's NUMBER OF FOLD ROUNDS Q.k AT LINK l IS THE k OF THE GROUP IN FRONT AT WHICH THE PROVED SUB-PROTOCOL's CONDITION IS SHOWN: FROM ONE EQUATION: THE FIRST CHAIN's REQUEST's SHAPE IS THE WRITTEN ONE. Statements and proofs.
WHY. K10's law is typed at a group gs in front (k10_condition_real_full, k10_public_full: gs.k = kLay of the l-th written list at the written request's flags). The seated sub-protocol's number Q.k is read off the first state's frame (ProofFile.k10Par: k := Gr.k,
Gr := Z.s₀.check.frame.groups[p.link]). That the two are one («hZ») was a run's word (GroupsGuard).
  par_k            ProofFile.k10Par Z xs p = some Q: Q.link = p.link, and there is Gr with Z.s₀.check.frame.groups[p.link]? = some Gr · Q.k = Gr.k · Q.h = Gr.h: off k10Par's text.
  first_groups     ProofFile.pureRoad.pub o pol lay KL = .ok Z: Z.s₀.check.frame.groups = reqGroups Z.first.shape: pub_start with Meaning.K2.recAll_first (Johnson/Goal/Meaning/RecAll.lean).
  k_of_shape       so, where Z.first.shape = shapeFull and p.link = l < 25: Q.k = kLay ‹the l-th written list› ‹the written request's flags› (ReqKept.lean's real_full, second clause: the kernel).
  k10_k_scope      in scope, at an opened description, under that one equation: at every sub-protocol b of c.blocksInOrder of the kind K10: l < 25, p, Q with k9At Z l = some p · k10Par … = some Q · c.blocksInOrder[ixK10 l]? = some b · Q.k = kLay ‹the l-th written list› ‹the flags›. (kLay … is what
                   k10_condition_real_full's and k10_public_full's gs.k is said to be: the join «Q.k = gs.k» is one rewriting, not typed here.)
LIMITS. **hsh : Z.first.shape = shapeFull IS A PREMISE.** first_shape_in_scope draws it, in scope, from a pin (firstPinnedAt Z.p.X.P Z.first = true) that the laid value does not ask yet: so under the gate's yes it is NOT yet paid. That p.link = l is
k9_alone's. Q.rows is not treated. Nothing on soundness.

-/
import Johnson.LPFK10R.SitsAll
import Johnson.IMR.RecRun
import Johnson.Desc.First.Close.Law.ReqKept

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (Par kbAt real_full kLay)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit)
open OnBytes
open ProofFile (Cl)
open IM

/-- What k10Par's yes says of the numbers k and h. -/
theorem par_k {Z : ProofFile.Pub} {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)}
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} (h : ProofFile.k10Par Z xs p = some Q) :
    Q.link = p.link ∧ ∃ Gr, Z.s₀.check.frame.groups[p.link]? = some Gr ∧ Q.k = Gr.k ∧ Q.h = Gr.h := by
  unfold ProofFile.k10Par at h
  obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Gr, hG, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, Gr, hG, rfl, rfl⟩
  · cases h

/-- The first state's frame's groups are those of the first chain's request's shape. -/
theorem first_groups {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.s₀.check.frame.groups = reqGroups Z.first.shape :=
  (Meaning.K2.recAll_first (Meaning.K2.pub_start h)).walk.groups

/-- **Q.k is the layout's formula at the written list and the written request's flags.** -/
theorem k_of_shape {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hsh : Z.first.shape = shapeFull)
    {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)} {p : VerifiableInference.Desc.K9.Where}
    {Q : Par} (hQ : ProofFile.k10Par Z xs p = some Q) (hl : p.link < 25) :
    Q.k = kLay (linksFullLit.getD p.link [])
      (kbAt shapeFull p.link (linksFullLit.getD p.link [])) := by
  obtain ⟨-, Gr, hG, ek, -⟩ := par_k hQ
  rw [first_groups h, hsh] at hG
  rw [ek, (real_full p.link hl).2.1, Array.getD_eq_getD_getElem?, hG]
  rfl

/-- **In scope, at an opened description, under the one equation: at every sub-protocol of the kind
K10 the number of fold rounds is the layout's formula's.** -/
theorem k10_k_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        c.blocksInOrder[ixK10 l]? = some b ∧
        Q.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) := by
  intro b hb hk
  obtain ⟨l, hl, Lk, p, Q, -, e2, e3, -, e5, -⟩ := k10_sits_each hS hR O b hb hk
  obtain ⟨-, p', -, f2, -, -, f5, -⟩ := k9_alone O l (subAt l) (subs_scope hS hR O l hl)
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans f2)
  have hk' := k_of_shape (o := OnBytes.secondHashFunction) O.pub hsh e3 (by rw [f5]; exact hl)
  rw [f5] at hk'
  exact ⟨l, hl, p, Q, e2, e3, e5, hk'⟩

end LPFK10

#print axioms LPFK10.k10_k_scope
#print axioms LPFK10.par_k
#print axioms LPFK10.first_groups
#print axioms LPFK10.k_of_shape
