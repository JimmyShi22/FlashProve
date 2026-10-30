-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroVia.lean: ITS FORM FIRST: 7 INSTANCES OF THE CLASS `StaysZ`
(Johnson/P1K8R/ZeroFl.lean) AND NO OTHER, ONE LOCAL MACRO ("staysZ"): AS
Johnson/Desc/First/Link/Law/LooksVia.lean HAS THEM FOR THE CLASS Stays. K3's SUB-PROTOCOL AT AN
ADDRESS, WHOLE (THE DECISION AND ITS RUNS OF CLAIMS), STANDS IN `KeepsZero`, WITH NO PREMISE ON THE
PLAN. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksVia.lean, WITH THE ROWS'
FIRST COLUMNS (`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND
`KeepsZero` IN THE PLACE OF KeepsLooks: every declaration of that file that names the looks, or
leans on one that does, under a new name; the others are called where they lie. None of the
library's goals. No prover stands in it; nothing on completeness, soundness or hiding.

  `kz_putFork`   a ledger with the same first columns is laid where one is open
  `via_decidesZ`, `via_wholeZ`, `viaW_callsZ`, `viaW_digitsZ`, `planesRun_kz`, `joinRun_kz`   there:
      the same names without "Z", with "keeps"
  `theOwn_wholeZ`, `theWhole_wholeZ`, **`theStated_wholeZ`**   the like
Limits. At the seats whose `mark` is the laying of the ledger. "Whole" is the library's Keeps.Whole
(Johnson/Desc/FoldKeeps.lean): the decision, every run of claims, every run behind the batching.
Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroSeated
import Johnson.Desc.First.Link.Law.LooksVia

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysZ" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysZ.bind ?_ ?_
    | intro _
    | split)

instance staysZ_paidF (i : ℕ) : StaysZ (paidF i) :=
  StaysZ.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameL0.refl F

instance staysZ_planesAddedF (g : Forest.Heard) : StaysZ (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance staysZ_joinAddedF (g : Forest.Heard) : StaysZ (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance staysZ_joinF (g : Forest.Heard) (KF : Array Aff) : StaysZ (joinF g KF) := by
  unfold joinF; staysZ

instance staysZ_planesAtF (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, StaysZ (bit a b)] : StaysZ (planesAtF g lm e bit) := by
  unfold planesAtF
  exact staysZ_foldlM (fun _ _ => by staysZ) _ _

instance staysZ_leavesRowOwn (p : Psc) (S0 : E) (kept : Aff) : StaysZ (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; staysZ

instance staysZ_planeClaimsOwn (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, StaysZ (bit a b)] [∀ a, StaysZ (pin a)] :
    StaysZ (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine StaysZ.bind inferInstance fun _ => ?_
  refine StaysZ.bind inferInstance fun _ => ?_
  refine StaysZ.bind inferInstance fun _ => ?_
  refine StaysZ.bind (staysZ_foldlM (fun _ _ => by staysZ) _ _) fun _ => ?_
  staysZ

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

section

/-- **The tool for a run**: a ledger with the same first columns is laid where one is open. -/
theorem kz_putFork {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : G.trees.map l0s = F.trees.map l0s) : KeepsZero s (s.putFork G) := by
  refine kzL_of_cases fun G' L' e1 e2 => Or.inr ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decidesZ {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides KeepsZero (K3.Law.blockVia seat piece laid before p guests) := by
  intro s rs gs s' h
  have h' : K3.Law.decideVia seat p s rs = .ok s' := h
  unfold K3.Law.decideVia at h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, hn, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain rfl := Except.ok.inj h'
  have hF' := named_some hF
  have hn' : seat.heard s = none := by
    cases e : seat.heard s with
    | none => rfl
    | some g =>
      rw [e] at hn
      exact nomatch hn
  have e1 : (seat.put s x.1 x.2).fork? = some x.2 := by
    rw [← hf]
    exact hk s x.1 x.2 (by rw [hF']; rfl) hn'
  refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact congrArg (·.map l0s) (ViaL.hearVia_arrays (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_wholeZ {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole KeepsZero (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decidesZ seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsZero s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact kz_putFork (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact kz_refl s

theorem viaW_callsZ {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole KeepsZero (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_wholeZ _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digitsZ {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole KeepsZero (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_wholeZ _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_kz {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl KeepsZero (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsZero s (seat.mark s x.2.1)
  rw [hm]
  refine kz_putFork (by rw [← hf]; exact named_some hF) ?_
  have i : FlL.StaysZ (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlL.StaysZ.bind inferInstance fun _ => ?_
    refine FlL.StaysZ.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_kz {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl KeepsZero (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsZero s (seat.mark s x.2.1)
  rw [hm]
  exact kz_putFork (by rw [← hf]; exact named_some hF)
    ((FlL.staysZ_joinF g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_wholeZ {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole KeepsZero b := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : Whole KeepsZero (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digitsZ claim a.piece laid sent p []
        | false => exact viaW_callsZ claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_wholeZ {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole KeepsZero b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_wholeZ claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole KeepsZero (kz_trans) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_kz hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_wholeZ {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole KeepsZero b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_wholeZ claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        refine ⟨W.1, fun c hc n => ?_, W.2.2⟩
        rcases List.mem_append.1 hc with hc | hc
        · exact W.2.1 c hc n
        · obtain rfl := List.mem_singleton.1 hc
          exact planesRun_kz _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kz_putFork
#print axioms VerifiableInference.Desc.LinkJoin.via_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.via_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.viaW_callsZ
#print axioms VerifiableInference.Desc.LinkJoin.viaW_digitsZ
#print axioms VerifiableInference.Desc.LinkJoin.planesRun_kz
#print axioms VerifiableInference.Desc.LinkJoin.joinRun_kz
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.theStated_wholeZ
