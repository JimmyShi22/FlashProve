-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/TablesWalk.lean: SMALL LAWS FOR THE WALK THAT CARRIES TablesOk
(Johnson/Desc/K1/Law/TablesOk.lean: where the output head's reads' tables are laid, they are what the
reads' quiet step would lay off this very state) ALONG THE REACHED STATES OF THE FIRST CHAIN. Typed
for the row "TablesOk along reached". Statements
with their proofs.

Part 1: behind a reads' place, and over the approximate range proof's sub-protocol.
  QuietT0 h L hp q    behind an accept of q the invariant holds, WITH NOTHING ASKED IN FRONT.
  quietT0_layers | _att | _head | _blockAt | _readsQuietAt | _orLoud: the reads' quiet step at each
                      sort of segment (behind the first two the state stands in no head).
  tablesOk_behind_reads   **behind the reads' place of ANY segment: no premise.**
  tablesOk_putTl      laying the approximate range proof's part anew keeps the invariant.
  quietT_small        **K8.whole p keeps it, at every p.**
What is not claimed. That it holds at a reached state. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K1.Law.TablesOk
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Here HeadOwn)
open OnBytes.Model.Stages (LinkH)

variable {Cl : Type}

/-! ## 1 Behind a reads' place -/

/-- Behind an accept of q the invariant holds; nothing is asked in front. -/
def QuietT0 (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (q : Block S Cl) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → TablesOk h L hp s'

section
variable (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2)

theorem quietT0_layers (P : K8.ReadsQuiet.PG) : QuietT0 h L hp (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs e
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok e
  intro a2 t h1 _
  cases h1

theorem quietT0_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietT0 h L hp q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs e
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq e
  intro a2 t2 h1 _
  cases h1

end

theorem quietT0_head (P : K8.ReadsQuiet.PH) : QuietT0 P.h P.L P.hp (K8.ReadsQuiet.head P) :=
  fun _ _ _ _ e => tablesOk_behind P e

theorem quietT0_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (e : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietT0 hS HLy H q := by
  unfold K8.ReadsQuiet.blockAt at e
  obtain ⟨k, -, e⟩ := Option.bind_eq_some_iff.1 e
  split at e
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 e
    exact quietT0_layers _ _ _ _
  · split at e
    · obtain rfl := Option.some.inj e
      exact quietT0_head _
    · cases e

theorem quietT0_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (e : ProofFile.readsQuietAt G l X piece = some q) :
    QuietT0 G.W.hS G.W.HLy G.W.H q := by
  unfold ProofFile.readsQuietAt at e
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at e
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at e
      exact quietT0_att _ _ _ e
    · rw [if_neg h2] at e
      cases e
  · rw [if_neg h1] at e
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at e
      exact quietT0_blockAt e
    · rw [if_neg h2] at e
      cases e

theorem quietT0_orLoud (name : String) (p : Place) (what : String) (G : ProofFile.Ground) (l : Nat)
    (X : LinkH) (piece : Nat) :
    QuietT0 G.W.hS G.W.HLy G.W.H (ProofFile.orLoud name p what (ProofFile.readsQuietAt G l X piece)) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none => exact fun s s' rs gs e => nomatch e
  | some q => exact quietT0_readsQuietAt l X _ q hq

theorem quietT0_joined (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (P : Par)
    (link moment : Nat) (arrays : Option (List Nat)) (nm : String) (q : Block S Cl)
    (hq : QuietT0 h L hp q) :
    QuietT0 h L hp (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs e
  have e' : ((commitAtS P link moment arrays : Block S Cl).decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := e
  obtain ⟨s₁, _, h2⟩ := (bind_ok _ _ _).1 e'
  exact hq _ _ _ _ h2

/-- **Behind the reads' place of any segment the invariant holds: no premise.** -/
theorem tablesOk_behind_reads (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (arrs : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (e : (blkL Z G₀ l false X arrs).decide s rs gs = .ok s') :
    TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s' :=
  quietT0_joined _ _ _ _ _ _ _ _ _ (quietT0_orLoud _ _ _ G₀ l X _) s s' rs gs e

/-! ## 2 Over the approximate range proof's sub-protocol -/

theorem tablesOk_putTl (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (s : S) (tl : HTailF2)
    (k : TablesOk h L hp s) : TablesOk h L hp (s.putTl tl) := by
  intro a' t ha' ht
  unfold S.putTl at ha'
  cases ha : s.here with
  | head a =>
    rw [ha] at ha'
    by_cases ho : a.opened = true
    · simp only [ho, if_true] at ha'
      obtain rfl := Here.head.inj ha'
      obtain ⟨cov, x, c1, c2, c3⟩ := k a t ha ht
      refine ⟨cov, x, ?_, c2, c3⟩
      have e : s.putTl tl = { s with here := .head { a with tl := tl } } := by
        unfold S.putTl
        rw [ha]
        simp only [ho, if_true]
      rw [e]
      exact c1
    · simp only [ho, if_false, Bool.false_eq_true] at ha'
      have e : s.putTl tl = s := by
        unfold S.putTl
        rw [ha]
        simp only [ho, if_false, Bool.false_eq_true]
      rw [e]
      rw [ha] at ha'
      obtain rfl := Here.head.inj ha'
      exact k a t ha ht
  | lay a =>
    rw [ha] at ha'
    cases ha'
  | att a =>
    rw [ha] at ha'
    cases ha'
  | _ =>
    rw [ha] at ha'
    simp only [ha] at ha'
    cases ha'

/-- **The approximate range proof's sub-protocol keeps the invariant, at every p.** -/
theorem quietT_small (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (p : First.K8.ParW) :
    QuietT h L hp (First.K8.whole p) := by
  intro s s' rs gs hd k
  have hd' : (First.K8.approximateRangeProofDrawKind (Cl := Claim) First.K8.atS p.toPar).decide s rs gs = .ok s' := hd
  obtain ⟨r, rfl⟩ := First.K8.decide_one _ p.toPar s s' rs gs hd'
  obtain ⟨tl, ht, hm⟩ := (First.K8.decide_atS_iff p.toPar s s' r gs).1 hd'
  rw [hm.2.2.2.2.2.2.2.2]
  exact tablesOk_putTl h L hp s _ k

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.quietT0_layers
#print axioms VerifiableInference.Desc.K1.quietT0_att
#print axioms VerifiableInference.Desc.K1.quietT0_head
#print axioms VerifiableInference.Desc.K1.quietT0_orLoud
#print axioms VerifiableInference.Desc.K1.quietT0_joined
#print axioms VerifiableInference.Desc.K1.tablesOk_behind_reads
#print axioms VerifiableInference.Desc.K1.tablesOk_putTl
#print axioms VerifiableInference.Desc.K1.quietT_small
