-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/PoweredAtStand.lean: THE SMALLNESS TEST: AT A STAND OF THE BATCHING
(`BatStand`, Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean, another house's file) THE LEDGER
BEHIND THE ADDING HAS THE DRAWN ELEMENT AS ITS BATCHING ELEMENT, AND THE TEST's DATA THERE CARRY THE
POWERS OF THAT ELEMENT (the library's `Powered`, OnBytes/Tie/Pv/Tail/EndClosed.lean). So the
heaviest premise of Johnson/Desc/ProofFile/Honest/K8/RestOf.lean is had at the ledger at which the
tests behind the adding are called. A joining; none of the library's goals.

  `tl_of_pair`, `block_lays`   the run that the kind's own block states under "K8.equations" lays
                   "the data's vectors of powers are the powers of θ" wherever the open ledger's
                   batching element is θ
  **`powered_at_stand`**   K8At Lk k pW → ThetaAt Lk Lk.order → Lk.order = pre ++ k8Entry k :: post
                   → PowOn Lk post → a stand ⊢ s'.fork? = some G ∧ G.theta = x ∧ PowAt x s'
  **`powered_laid`**   so, at the data behind the batching with the kept slots laid: Powered { tl
                   with lsTail := … } G.theta
  **`powered_layers`**, **`powered_attention`**, **`powered_head`**   AT A LINK OF EACH SORT: from
                   the sort's ties, K8At, and ONE SENTENCE AT THE LOOKUPS' ENTRIES: that their runs
                   hand on "a ledger is open and its batching element is θ" (`ThetaAt`)
THE ROAD: the draw lays the element (the other house's `draw_iff`, `draw_facts`) · along the order:
`ran_lays` (Johnson/Desc/ProofFile/Honest/K8/RanLays.lean); the kind's own run lays the second
sentence (`powered_of_yes`, Johnson/Desc/K8/Honest/PoweredOfYes.lean); behind it the sort's own ties
hand it on (Johnson/Desc/K8/Honest/PowBehind.lean) · the adding leaves the element (`addList_theta`,
Johnson/Desc/K8/Honest/AddTheta.lean) and the data (the library's `tl_set`) · that G is the ledger
behind is the other house's own field · the laying of the kept slots leaves what the six clauses of
`Powered` read.
Limits. IMPLICATIONS: `K8At`, THE SORT's TIES AND `ThetaAt` AT THE LOOKUPS' ENTRIES (two at a
feed-forward link, four at an attention link, three at the head's) ARE PREMISES. Of the lookups'
runs nothing is asked on the test's data: in the library's three orders they all stand in front of
"K8.equations".
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.RunAtStand
import Johnson.Desc.ProofFile.Honest.K8.RanLays
import Johnson.Desc.K8.Honest.ThetaRunAt
import Johnson.Desc.K8.Honest.PowBehind
import Johnson.Desc.K8.Honest.AddTheta
import Johnson.Desc.First.Batch.Law.KeepsTl
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP equations)
open VerifiableInference.Desc.First.TailClaims.Law (partOf sits_equations)
open VerifiableInference.Desc.First.K8.Honest (parts_of PowAt ThetaAt powered_of_yes addList_theta
  thetaRun_layers thetaRun_attention thetaRun_head)
open VerifiableInference.Desc.K9L (Bound GE8)
open VerifiableInference.Desc.PhiAll (Phi)
open VerifiableInference.Desc.LinkJoin (Q HasFork PowOn SegAt LayersTake AttTake HeadTake powOn_nil
  powOn_layers powOn_head split_layers split_attention split_head)
open ProofFile.Honest.K9 (BatStand gathered gather_ran k8Entry drawnOne draw_facts draw_iff)

/-- The data, off the pair of the data and the ledger. -/
theorem tl_of_pair {u : S} {t : HTailF2} {F : Fork} (h : tlForkP.get? u = some (t, F)) :
    u.tl? = some t := by
  obtain ⟨t', ht, h3⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨F', -, e⟩ := Option.map_eq_some_iff.1 h3
  obtain rfl : t' = t := congrArg Prod.fst e
  exact ht

/-- **The run that the kind's own block states lays the sentence.** -/
theorem block_lays (θ : E) (pW : K8.ParW) (runK : Nat → S → Except String (List Claim × S))
    (h8 : ("K8.equations", runK) ∈ (K8.whole pW).claims) (n : Nat) (e e₁ : S) (c : List Claim)
    (hr : runK n e = .ok (c, e₁)) (hθ : HasFork (fun G => G.theta = θ) e) : PowAt θ e₁ := by
  obtain ⟨q, tl', F1, hq, he, rfl⟩ := (sits_equations pW runK h8 n e e₁ c).1 hr
  obtain ⟨-, -, hF⟩ := parts_of hq
  obtain ⟨G, hG, rfl⟩ := hθ
  obtain rfl : G = q.F := Option.some.inj (hG.symm.trans hF)
  have hg : tlForkP.get? e = some (q.tl, q.F) := by
    unfold partOf k8PartP at hq
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨fs, -, rfl⟩ := Option.map_eq_some_iff.1 h2
    exact hx
  have hs : tlForkP.get? (k8PartP.set e { q with tl := tl', F := F1 }) = some (tl', F1) :=
    tlForkP_lawful.get_set e _ _ hg
  exact ⟨tl', tl_of_pair hs, powered_of_yes he⟩

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} {Lk : Link S Claim} {p : Desc.K9.Where}
  {T : Thread Bk S Claim V W X Pb} {b : Nat}
  {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} {x : E}
  {z : S × Desc.K9.Part × List Claim} {G : Fork}

/-- **At a stand: the drawn element, and its powers in the data.** -/
theorem powered_at_stand {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    s'.fork? = some G ∧ G.theta = x ∧ PowAt x s' := by
  have hg := hS.bat.gathered
  cases hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] with
  | error e => simp [gathered, hd] at hg
  | ok t₁ =>
    cases hy : claimsInBy Lk.each Lk.hear Lk.order t₁ with
    | error e => simp [gathered, hd, hy] at hg
    | ok yy =>
      have hg' : (Desc.K9.atS.get? yy.2).map (fun a' => (yy.2, a', yy.1)) = some z := by
        simp only [gathered, hd, hy] at hg
        exact hg
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 hg'
      obtain ⟨a, ha, -⟩ := (draw_iff p s x).1 ⟨t₁, hd⟩
      obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a ha hd
      have h0 : HasFork (fun G => G.theta = x) t₁ := ⟨a₁.F, Desc.K9.get_fork t₁ a₁ h1, hl.chi⟩
      obtain ⟨ls, -, hRan⟩ := gather_ran Lk.each Lk.hear Lk.order t₁ yy hy
      rw [hsp] at hRan
      obtain ⟨hI, hJ⟩ := ran_lays Lk.hear (HasFork fun G => G.theta = x) (PowAt x) (k8Entry k)
        post
        (fun o ho run hr n t zz hIt hJt hz => hPw x o ho run hr n t zz.1 zz.2 hz hIt hJt)
        (fun run hr n t zz hIt hz => by
          obtain ⟨runK, h8, hu⟩ := hK.2 run hr
          exact block_lays x pW runK h8 n t zz.2 zz.1 (hu n t zz hz) hIt)
        pre 0 t₁ ls yy.2
        (fun o ho run hr n t zz hIt hz => hTh x o (hsp ▸ ho) run hr n t zz.1 zz.2 hz hIt)
        h0 hRan
      obtain ⟨F, hF, hx⟩ := hI
      obtain rfl : F = a'.F := Option.some.inj (hF.symm.trans (Desc.K9.get_fork yy.2 a' ha'))
      refine ⟨hS.bat.ledger, (addList_theta _ _ _ hS.bat.added).trans hx, ?_⟩
      obtain ⟨tl, ht, hP⟩ := hJ
      refine ⟨tl, ?_, hP⟩
      rw [hS.bat.state]
      exact (K9L.tl_set _ _).trans ht

/-- **So at the data with the kept slots laid.** -/
theorem powered_laid {tl : HTailF2} (h : G.theta = x ∧ PowAt x s') (ht : s'.tl? = some tl)
    (v : Array E) : Powered { tl with lsTail := v } G.theta := by
  obtain ⟨hx, tl₀, ht₀, hP⟩ := h
  obtain rfl : tl₀ = tl := Option.some.inj (ht₀.symm.trans ht)
  rw [hx]
  exact ⟨hP.vp, hP.vt, hP.rowX, hP.loX, hP.eqFirst, hP.shape⟩

variable {β : Type} {l : ℕ} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
  {pW : K8.ParW}

/-- **At a feed-forward link.** -/
theorem powered_layers (hL : SegAt l .layers Lk) {p4 : OnBytes.Desc.First.K4.Par}
    (A : LayersTake Lk u ψ Ok Fu p4 nU ent tm4 t3 l3)
    (k3 : ThetaAt Lk [(1, "objects"), (6, "objects")]) (hK : K8At Lk .layers pW)
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    s'.fork? = some G ∧ G.theta = x ∧ PowAt x s' :=
  powered_at_stand hK (thetaRun_layers hL A k3).1 (split_layers hL) (powOn_layers A) hS

/-- **At an attention link.** -/
theorem powered_attention (hL : SegAt l .attention Lk)
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake Lk u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3 : ThetaAt Lk [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")])
    (hK : K8At Lk .attention pW) (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    s'.fork? = some G ∧ G.theta = x ∧ PowAt x s' :=
  powered_at_stand hK (thetaRun_attention hL A k3).1 (split_attention hL) (powOn_nil Lk) hS

/-- **At the head's link.** -/
theorem powered_head (hL : SegAt l .head Lk) {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {pH : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake Lk u ψ Ok Fu h iU3 l' piece pH kap nU ent tm4 t3 l3)
    (k3 : ThetaAt Lk [(2, "objects"), (2, "planes"), (7, "objects")]) (hK : K8At Lk .head pW)
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    s'.fork? = some G ∧ G.theta = x ∧ PowAt x s' :=
  powered_at_stand hK (thetaRun_head hL A k3).1 (split_head hL) (powOn_head A) hS

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.block_lays
#print axioms ProofFile.Honest.K8.powered_at_stand
#print axioms ProofFile.Honest.K8.powered_laid
#print axioms ProofFile.Honest.K8.powered_layers
#print axioms ProofFile.Honest.K8.powered_attention
#print axioms ProofFile.Honest.K8.powered_head
