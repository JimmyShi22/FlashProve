-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RidesAtMgR.lean: «AN ACCEPTING TRANSCRIPT HANDS THE CONDITION ON», AT
THE CONDITIONS OF THE SECOND FORM OF THE CHAIN OF PROMISES (`onTR`, LinkTiedR.lean: the table's
promise, no mark, and a condition Rch that every accepting step hands on), AT THE COMPOSED MEANING
(`mgAll 𝔇 mgBase`), OVER A LINK's FOUR SUB-PROTOCOLS OF THE BATCHING KIND AND THE FRAME (our files
call a sub-protocol a block). RidesAtMg.lean's three and EqMg.lean's one, with each premise that was
asked «wherever the promise holds» now asked ONLY WHERE Rch HOLDS TOO. Theorems.

What is said.
  `h01_mgR`, `h12_mgR`, `hon3_mgR`, `hands_mgR`: **`onTR … k a` and the piece's accepting transcript
    give `onTR … (k + 1) b`.** The premises `OracleAsks`, «the one sum can be taken» behind the
    frame's sub-protocol, `EqAsks` and hg take Rch k a in front: so a fact that is shown along the
    verifier's run from the state at the start may pay them.

Limits. Rch is a letter; its hand-on at the piece is a premise. The premises are weaker than
RidesAtMg.lean's and EqMg.lean's, not paid. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.EqMg
import Johnson.Desc.First.Link.Law.LinkTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers rowsAtFit)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

section
variable (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
  (Rch : ℕ → S × F.E.Str → Prop) (k m : ℕ) (p p' : Place)

/-- **h01, SECOND FORM.** -/
theorem h01_mgR (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 1)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pb : Piece C F S Claim WT)
    (hpb : pb.b = below L.batchB) (H : HandsOn Rch k pb)
    (O : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pb.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pb.base a.1 b.1) :
    ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pb.ior.red.out a τ = some b →
      onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨hn, hq, hw⟩ := fit_batch links pl hfit k m p p' hp hp' hl hpc
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  have hs := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha.1).1
  exact ⟨onT_rides Nm (mgAll 𝔇 mgBase) links pl z k p hp hq a b
    (rec_of_rb Nm links pl k p p' hp hp' ⟨hn.1, hn.2⟩ ht hm a b (h.two.1 _ _ _ _ _ j hstep).1
      (Or.inr hw) hs)
    (mgRides_at 𝔇 Nm links pl z k m 1 p hpf hp hl hpc (Or.inl rfl) a b
      (quiet_batch 𝔇 Nm links pl z k m L pp h pb hpb a b τ hout (O a τ b ha hout))) ha.1,
    H a τ b ha.2 hout⟩

/-- **h12, SECOND FORM.** -/
theorem h12_mgR (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 2)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (h : LinkShare L pp) (pq : Piece C F S Claim WT)
    (hpq : pq.b = below L.behindB) (H : HandsOn Rch k pq)
    (O : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pq.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k pq.base a.1 b.1)
    (T : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pq.ior.red.out a τ = some b → K9.totalIn (𝔇.pubD.N.group m) b.1 = true) :
    ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pq.ior.red.out a τ = some b →
      onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨hn, hq, hw⟩ := fit_behind links pl hfit k m p p' hp hp' hl hpc
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  have hs := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha.1).1
  exact ⟨onT_rides Nm (mgAll 𝔇 mgBase) links pl z k p hp hq a b
    (rec_of_rb Nm links pl k p p' hp hp' ⟨hn.1, hn.2⟩ ht hm a b (h.two.2 _ _ _ _ _ j hstep).1
      (Or.inr hw) hs)
    (mgRides_at 𝔇 Nm links pl z k m 2 p hpf hp hl hpc (Or.inr (Or.inl rfl)) a b
      (quiet_behind 𝔇 Nm links pl z k m L pp h pq hpq a b τ hout (O a τ b ha hout)
        (T a τ b ha hout))) ha.1,
    H a τ b ha.2 hout⟩

/-- **hon3, SECOND FORM.** -/
theorem hon3_mgR (hfit : linkFit links pl = true) (hlf : listFit links pl = true)
    (hpf : pubFitE moreAll links pl = true) (hN : rowsAtFit Nm links.length = true)
    (hml : m < links.length) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim WT) (hpe : pe.b = below b₃) (H : HandsOn Rch k pe)
    (hg : ∀ a : S × F.E.Str, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      ∀ x, atS.get? a.1 = some x → Nm.groupAt m = x.L.check.group)
    (A : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pe.ior.red.out a τ = some b → EqAsks 𝔇 Nm links pl z k pe.base a.1 b.1) :
    ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      pe.ior.red.out a τ = some b →
      onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨hn, hins, houts, fresh, seg⟩ := fit_eq links pl hfit k m p p' hp hp' hl hpc
  obtain ⟨hat, inj⟩ := numbers_of_fit Nm links pl hN hlf k m p hp hl hpc hml
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨x, row, G0, hx, hG, El⟩ := eq_lays pw b₃ hb₃ _ _ _ _ _ j hstep
  obtain ⟨h1, h2, h3, _, _, h6⟩ := onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha.1
  refine ⟨onT_rides_nopin Nm (mgAll 𝔇 mgBase) links pl z k p hp (by rw [hins]; simp [Item.isPin])
    (by rw [houts]; simp [Item.isPin]) a b El.failed ?_
    (eq_rows Nm _ _ m hins houts fresh seg hat inj a.1 b.1 _ row G0 El hG (hg a ha x hx) h2)
    (eq_members Nm _ _ m hins houts fresh seg a.1 b.1 _ row El h3)
    (eq_book Nm _ _ ht hm a.1 b.1 _ row El h6)
    (mgRides_eq 𝔇 Nm links pl z k m p hpf hp hl hpc pw b₃ hb₃ pe hpe a b τ hout (A a τ b ha hout))
    ha.1, H a τ b ha.2 hout⟩
  rw [hp] at h1
  rw [hp']
  exact eq_shape links p p' ⟨hn.1, hn.2⟩ a.1 b.1 _ row El h1

/-- **THE SHUTTING's «hands», SECOND FORM.** -/
theorem hands_mgR (hfit : linkFit links pl = true) (hpf : pubFit9 true moreAll links pl = true)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 5)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅) (H : HandsOn Rch k ps)
    (O : ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      ps.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp Nm links pl z k ps.base a.1 b.1) :
    ∀ a τ b, onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch k a →
      ps.ior.red.out a τ = some b →
      onTR Nm (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rch (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨hn, hq, hnw⟩ := fit_shut links pl hfit k m p p' hp hp' hl hpc
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨R, e⟩ := rb_shutB pw piece b₅ hb₅ _ _ _ _ _ j hstep
  have hs := (onT_bools Nm (mgAll 𝔇 mgBase) links pl z k a ha.1).1
  have hwait : b.1.noneWaits = true := by
    have hs0 := hs
    rw [hp] at hs0
    have hs' : (First.standOf a.1 == First.standAt links p &&
        (a.1.noneWaits || First.mayWait links p) &&
        a.1.link?.all fun L => p.link == some L.link) = true := hs0
    have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hs').1).2
    rw [hnw, Bool.or_false] at h2
    unfold S.noneWaits at h2 ⊢
    rw [e]
    exact h2
  exact ⟨onT_rides Nm (mgAll 𝔇 mgBase) links pl z k p hp hq a b
    (rec_of_rb Nm links pl k p p' hp hp' ⟨hn.1, hn.2⟩ ht hm a b R (Or.inl hwait) hs)
    (mgRides_at 𝔇 Nm links pl z k m 5 p hpf hp hl hpc (Or.inr (Or.inr rfl)) a b
      (quiet_shut 𝔇 Nm links pl z k m pw piece b₅ hb₅ ps hps a b τ hout (O a τ b ha hout))) ha.1,
    H a τ b ha.2 hout⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.h01_mgR
#print axioms VerifiableInference.Desc.LinkJoin.h12_mgR
#print axioms VerifiableInference.Desc.LinkJoin.hon3_mgR
#print axioms VerifiableInference.Desc.LinkJoin.hands_mgR
