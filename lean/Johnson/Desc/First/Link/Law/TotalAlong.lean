-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TotalAlong.lean: THE PUBLIC TEST `totalIn`
(Johnson/Desc/First/Batch/FormsIn.lean) BEHIND THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING, FROM
WHAT HOLDS IN FRONT OF THE BATCHING. Theorems: joinings of
Johnson/Desc/First/Link/Law/LooksAre.lean, CoefsFit.lean, TotalBehind.lean, SeatsRide.lean and
SizedRides.lean. No text already in the library turns.

  `fork_behind`: whatever property of the open ledger the runs behind the batching keep passes an
    accepting step of the frame's sub-protocol behind it.
  `sizedLooks_batch`: an accepting step of the batching hands on: the ledger has its sizes, a sum a
    slot, and the looks.
  `totalIn_along`: **two accepting steps, of the batching from s₀ to s₁ and of the sub-protocol
    behind it from s₁ to s₂. IN FRONT, AT s₀: the ledger is well laid (`ledgerOk`); it has the looks
    sh; the mask row's message is seated and each array below sh's length is there (`SeatsThere`).
    THEN `totalIn own s₂ = true`**: ALL FOUR SHARES: the sizes ride (SizedRides.lean's rules); the
    seats ride (`Rs`); the range is sh's length; the weights' numbers are made by the run of self
    tests, the order's last.
  ITS OTHER PREMISES: the batching is the draw with the adding (`DrawMoves`) · THE RUNS' SHARE, FOUR
    TIMES: every run of the link's two orders hands on `SizedLooks sh` and stands in `Rs` (at the
    known runs: `rests_fork (sizedLooks_rests sh)`, `rests_rs`) · the order behind the batching ends
    in an entry whose run stands under `k8Tests nU` · `sortsB sh tl` at the range proof's structure
    in front of that run · a part is there at s₂.
Limits. AN IMPLICATION: none of the premises is shown of a link here; `sortsB` is evaluated at a
small configuration alone (LooksAtSmall.lean [not in this library]). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TotalBehind
import Johnson.Desc.First.Link.Law.SeatsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.K9 (atS Where totalIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- Whatever the runs behind the batching keep of the open ledger passes the sub-protocol. -/
theorem fork_behind (P : Fork → Prop) (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork P e → HasFork P e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hl : HasFork P s) : HasFork P s' :=
  ran_holds (HasFork P) L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _
      (Link.afterIn_of_runBehind (runBehind_of_step L ft s rs cols s' k h)))
    (fun o ho run hl x x₁ hr hx => hk o ho run hl x x₁ hr hx) hl

/-- **The batching hands on the sizes, a sum a slot, and the looks.** -/
theorem sizedLooks_batch (sh : List Look) (L : Link S Claim) (p : Where)
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hk : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.batchB.step ft s rs cols = .ok (s', k)) (hs : ledgerOk s = true)
    (hl : HasFork (LooksAre sh) s) : HasFork (SizedLooks sh) s' := by
  obtain ⟨r, x, a, o, cls, _, _, ha, hd, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, hq, hadd, rfl⟩, ⟨rfl, _⟩, _⟩ := hy
  obtain ⟨F0, hF0, hS0⟩ := (ledgerOk_iff s).1 hs
  obtain rfl : F0 = a.F := Option.some.inj (hF0.symm.trans (fork_part s a ha))
  obtain ⟨F0', hF0', hl0⟩ := hl
  obtain rfl : F0' = a.F := Option.some.inj (hF0'.symm.trans (fork_part s a ha))
  obtain ⟨hsame, hLS⟩ := drawn_same _ _ _ _ _ _ _ hd
  have hls : a.F.LS.size = a.F.ns := (drawnClean_tests _ _ _ _ _ _ _ hd).2.2.2.2.2.2.1
  have h0 : HasFork (SizedLooks sh)
      (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) :=
    ⟨o.F, fork_of_set s _ (by rw [ha]; rfl), ⟨sized_same hsame hS0, by
      rw [hLS, hsame.ns]; exact hls⟩, looks_draw _ _ _ _ _ _ _ hd hl0⟩
  have h1 : HasFork (SizedLooks sh) e :=
    gather_holds (HasFork (SizedLooks sh)) (fun _ => []) []
      (runsIn L.hear L.order)
      (fun r' hr' n e0 c0 e1 hr0 hx => by
        obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
        obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
        exact hk o' ho' run hrun n e0 c0 e1 hr0 hx) ([], _) (c, e)
      (fold_gstep L.each L.hear L.order ([], _) (c, e) hg) h0
  obtain ⟨F1, hF1, ⟨hS1, hL1⟩, hk1⟩ := h1
  obtain rfl : F1 = q.F := Option.some.inj (hF1.symm.trans (fork_part e q hq))
  have ht := addAll_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ c q.F G hL1 hadd
  refine ⟨G, fork_of_set e _ (by rw [hq]; rfl), ⟨?_, ht.2.2.1⟩, looks_add hL1 hadd hk1⟩
  rw [ht.2.1]
  exact hS1

/-- **THE PUBLIC TEST BEHIND THE TWO SUB-PROTOCOLS, FROM WHAT HOLDS IN FRONT OF THE BATCHING.** -/
theorem totalIn_along (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ) (L : Link S Claim)
    (p : Where) (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (k1 : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (r1 : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → Rs e e₁)
    (k2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (r2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (ft ft' : ℕ) (s₀ s₁ s₂ : S) (rs rs' : List Fmt.RoundView) (cols cols' : List OpenedColumn) (j j' : ℕ)
    (h₁ : L.batchB.step ft s₀ rs cols = .ok (s₁, j))
    (h₂ : L.behindB.step ft' s₁ rs' cols' = .ok (s₂, j'))
    (hs : ledgerOk s₀ = true) (hl : HasFork (LooksAre sh) s₀)
    (hseat : SeatsThere own sh.length s₀)
    (hB : ∀ e tl, k8Tests nU e = .ok s₂ → e.tl? = some tl → sortsB sh tl = true)
    (a : K9.Part) (ha : atS.get? s₂ = some a) : totalIn own s₂ = true := by
  have g1 := sizedLooks_batch sh L p hb₁ k1 ft s₀ rs cols s₁ j h₁ hs hl
  obtain ⟨G, hG, ⟨hS, hLS⟩, _⟩ := fork_behind (SizedLooks sh) L k2 ft' s₁ rs' cols' s₂ j' h₂ g1
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans (fork_part s₂ a ha))
  have hr : Rs s₀ s₂ := (rs_batch L p hb₁ r1 ft s₀ rs cols s₁ j h₁).trans
    (rs_behind L r2 ft' s₁ rs' cols' s₂ j' h₂)
  obtain ⟨t2, t3⟩ := seats_ride own sh.length hr a ha hseat
  obtain ⟨e, ⟨Fe, hFe, _, hle⟩, ht⟩ := full_runBehind (HasFork (SizedLooks sh)) nU L pre oT hord hT
    (fun o' ho' => k2 o' (by rw [hord]; exact List.mem_append_left _ ho')) s₁ s₂
    (runBehind_of_step L ft' s₁ rs' cols' s₂ j' h₂) g1
  exact totalIn_tests sh own nU e s₂ a ht ha ⟨Fe, hFe, hle⟩ (fun tl => hB e tl ht)
    ⟨hLS, hS.1, hS.2.1⟩ t2 t3

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fork_behind
#print axioms VerifiableInference.Desc.LinkJoin.sizedLooks_batch
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_along
