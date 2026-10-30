-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SitsLaw.lean: BEHIND Sits.lean: «… OR ITS YES GIVES THAT LAW's PREMISE»: the law of a sending (send_goodIn, Johnson/Desc/K1/Law/GoodSend3.lean)
speaks of no one constant: it speaks of ANY block b with IsSend P stOf b, under condPort P rad = true. Here both premises are paid AT THE DESCRIPTION's OWN
ENTRY b, in scope:
  isSend_underR     IsSend goes down along Block.UnderR (the like along Block.Under is K1.isSend_under, Johnson/Desc/K1/Law/AtTable.lean)
  isSend_retype     and over Block.retype
  leaves_blockAt    the reads' quiet step at a layers' link or the head's, as Johnson/Desc/K8/ReadsQuietAt.lean's blockAt hands it, leaves the messages
  leaves_k1Quiet    so does what the lot joins behind the reads (orLoud of readsQuietAt): at a layers' link and the head's outright; at an attention link
                    UNDER A NAMED PREMISE on that kind's own quiet step (LeavesAtt); where no block could be made the refuser never says yes
  LawAt b k P       IsSend P (·.st) b ∧ ∃ rad, condPort P rad = true, with PlaceOk 2 0 k P
  k01_law_digits    at all 25 links: outright
  k01_law_reads     at all 25 links: under LeavesAtt
  k01_law_first     at link 0's first place: IN THE ARM «ALONE» of LaidFramed; in the other arm a block of the frames' lot is joined
                    behind: not here.
What is not claimed. As Sits.lean. That an attention link's quiet step leaves the messages. send_goodIn's other premises (the rounds' draws; the readers;
the promises in front and behind). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Sits
import Johnson.Desc.K1.Law.GoodSendPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open ProofFile (Cl)
open IM (Open LaidAlone LaidFramed k1Reads k1Quiet k1Ix k1PlaceL k1Place0)

theorem isSend_underR {T C : Type} {P : Par} {stOf : T → Statement} {c b : Block T C}
    (u : c.UnderR b) (h : IsSend P stOf b) : IsSend P stOf c :=
  fun s s' r₁ r₂ gs hy => h s s' r₁ r₂ gs (u.2 _ _ _ _ hy)

theorem isSend_retype {T C C' : Type} {P : Par} {stOf : T → Statement} {b : Block T C}
    (h : IsSend P stOf b) : IsSend P stOf (b.retype : Block T C') :=
  fun s s' r₁ r₂ gs hy => h s s' r₁ r₂ gs hy

theorem leaves_blockAt {G : Array OnBytes.Model.Layer.HPlan2} {hS : OnBytes.Model.Head.Shape}
    {HLy : OnBytes.Model.Head.HL} {H : OnBytes.Model.Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat}
    {q : Block S Unit} (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) :
    LeavesMsgs (fun s : S => s.st) q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact leaves_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact leaves_head _
    · cases h

/-- The one premise on another kind's text: an attention link's quiet step behind the reads leaves the messages. -/
def LeavesAtt (G : ProofFile.Ground) : Prop :=
  ∀ (l g : Nat) (q : Block S Unit), First.Att.readsAtO G.W l g = some q →
    LeavesMsgs (fun s : S => s.st) q

theorem leaves_readsQuietAt {G : ProofFile.Ground} (hA : LeavesAtt G) (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) :
    LeavesMsgs (fun s : S => s.st) q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact hA _ _ _ h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact leaves_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem leaves_k1Quiet {G : ProofFile.Ground} (hA : LeavesAtt G) (l : Nat) (X : LinkH) :
    LeavesMsgs (fun s : S => s.st) (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact leaves_readsQuietAt hA l X _ q hq

/-- Both premises of the sending's law that speak of the block and of the plan's numbers. -/
def LawAt (b : Block S Cl) (k : Nat) (P : Par) : Prop :=
  IsSend P (fun s : S => s.st) b ∧ PlaceOk 2 0 k P ∧ ∃ rad, condPort P rad = true

theorem lawAt_of {b : Block S Cl} {k : Nat} {P : Par} (h : IsSend P (fun s : S => s.st) b)
    (hp : PlaceOk 2 0 k P) : LawAt b k P :=
  ⟨h, hp, by obtain ⟨y, -, -, hc⟩ := hp; exact ⟨_, hc⟩⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **At every link's digits' place the description's own entry pays the law's two premises.** -/
theorem k01_law_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l true]? = some b ∧
      LawAt b (3 * l + 2) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) := by
  intro l hl
  obtain ⟨Lk, b, digits, e1, e2, h, hp⟩ := k01_sits_digits hS hR O hc hs l hl
  exact ⟨Lk, b, e1, e2, lawAt_of (isSend_underR (IM.alone_underR h)
    (isSend_retype (isSend_commitAtS _ _ _ _))) hp⟩

/-- **At every link's reads' place**, under the one premise on the attention links' quiet step. -/
theorem k01_law_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hA : LeavesAtt Bs.G₀) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l false]? = some b ∧
      LawAt b (3 * l + 1) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) := by
  intro l hl
  obtain ⟨Lk, b, Xl, reads, e1, e2, -, h, hp⟩ := k01_sits_reads hS hR O hc hs l hl
  refine ⟨Lk, b, e1, e2, lawAt_of (isSend_underR (IM.alone_underR h) (isSend_retype ?_)) hp⟩
  exact isSend_andThen _ _ _ _ _ (isSend_laterAt _ _ _ _ _ _) rfl (leaves_k1Quiet hA l Xl)

/-- **At link 0's first place**, in the arm in which the block stands alone. -/
theorem k01_law_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[0]? = some Lk ∧ Lk.hear[0]? = some b ∧
      PlaceOk 2 0 0 (firstPar Bs.G₀.first (gpOf Z)) ∧
      (LaidAlone ProofFile.sameReply b (firstSegmentOpening Bs.G₀.first (gpOf Z) : Block S Unit).retype b.name k1Place0 →
        LawAt b 0 (firstPar Bs.G₀.first (gpOf Z))) := by
  obtain ⟨Lk, b, e1, e2, -, hp⟩ := k01_sits_first hS hR O hc hs
  exact ⟨Lk, b, e1, e2, hp, fun h => lawAt_of (isSend_underR (IM.alone_underR h)
    (isSend_retype (isSend_firstAtS _ _))) hp⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.leaves_k1Quiet
#print axioms VerifiableInference.Desc.K1.k01_law_digits
#print axioms VerifiableInference.Desc.K1.k01_law_reads
#print axioms VerifiableInference.Desc.K1.k01_law_first
