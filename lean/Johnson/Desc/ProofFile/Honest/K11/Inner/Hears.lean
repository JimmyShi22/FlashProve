-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Hears.lean: the proof of `HeadMergeHears`
(Honest/K11/Inner/Statement.lean), to the letter: where the part's `hear` returns on the sumcheck's
rounds, the kind's maker of the tape and its `mergeHear` return: the same ledger; the same letters.

How. What `hear` has read is written out by the library's `hear_spec`, `readAll_spec`
(Johnson/Desc/Part/MaskedSumShape.lean). Of that the strict maker's tape is made round by round
(`roundS_of_sent`, `tapeS_plain`, `headMerge_tape`). On that tape the library's flat text of the
merge returns (Honest/K11/Inner/FlatEnd.lean), and so the kind's text (`hear_of_flat`,
Johnson/Top/H0/MergeLaw/Flat.lean). The record that it hands back has ended (`endP_ended`,
OnBytes/Desc/First/P1/EndedOf.lean), so it has the letters of the part's record (`flatEnded`,
Johnson/Desc/Part/MaskedSumFlatProofs.lean).

Limits. Those of the statement. Nothing on soundness, on an honest prover or on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Inner.Statement
import Johnson.Desc.ProofFile.Honest.K11.Inner.FlatEnd
import Johnson.Desc.Part.MaskedSumFlatProofs
import Johnson.Top.H0.MergeLaw.Flat
import OnBytes.Desc.First.P1.EndedOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E addE mulE zeroE)
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork Psc WsLay WsClaim WsForkOut WsMerged wsForkStart wsRowPart wsEpsT powers
  RoundName)
open OnBytes.PscRun (Sized Filled)
open OnBytes.K.Kc (Fl Tape flatForkEnd flatOf)
open OnBytes.Desc.First.P1 (bind_eq must_eq rd runP endP Rnd Held held_atZero endP_row_ready
  endP_ended shown_returns)
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First.Look (elemsOf roundS tapeS kindAsked)
open VerifiableInference.Desc.First.Door (batchEntryB batchRoundB)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat claimFits_eq)
open VerifiableInference.Desc.Part.MaskedSum (Var Heard hear scalars Sent VarsRead hear_spec
  readAll_spec LensT ownSlots SameLetters heardAs flatEnded)
open Johnson.Desc.First.ForkMerge (mergeHear mergeTapeE mergeEntries claimFits)

/-! ## The tape -/

theorem elemsOf_scalars : ∀ l : List Fmt.ItemValue, elemsOf l = scalars l
  | [] => rfl
  | .e x :: l => by
    show (elemsOf l).map _ = (scalars l).map _
    rw [elemsOf_scalars l]
  | .f _ :: _ => rfl
  | .word _ :: _ => rfl
  | .root _ :: _ => rfl
  | .answer _ :: _ => rfl

/-- A round that holds just these scalars and drew just these elements, and elements alone, under an
entry that states as many draws, no position, no matrix entry and no row. -/
theorem roundS_of_sent {r : Fmt.RoundView} {n k : Nat} {s d : List E} (h : Sent r n k s d)
    (hp : r.drawn.poss = []) (ht : r.drawn.trits = []) (e : Fmt.Entry) (h1 : e.drawE = k)
    (h2 : e.poss = 0) (h3 : e.trits = 0) (h4 : e.rows = 0)
    (h5 : (e.name != RoundName.batSigma.name) = true)
    (h6 : (OnBytes.Params.kindOf e.name == some (kindAsked e.name)) = true) :
    roundS r e = some ⟨some e.name, e.drawNZ, 0, s, d⟩ := by
  obtain ⟨a1, _, a3, a4⟩ := h
  subst a4
  unfold roundS
  rw [elemsOf_scalars, a1]
  simp [a3, h1, hp, ht, h2, h3, h4, h5, h6]

theorem name_eps_ne : (RoundName.pscEpsilon.name != RoundName.batSigma.name) = true := by decide
theorem name_round_ne : (RoundName.pscRound.name != RoundName.batSigma.name) = true := by decide
theorem name_y_ne : (RoundName.pscY.name != RoundName.batSigma.name) = true := by decide
theorem name_values_ne : (RoundName.pscValues.name != RoundName.batSigma.name) = true := by decide
theorem kind_eps_asked : (OnBytes.Params.kindOf RoundName.pscEpsilon.name ==
    some (kindAsked RoundName.pscEpsilon.name)) = true := by decide
theorem kind_round_asked : (OnBytes.Params.kindOf RoundName.pscRound.name ==
    some (kindAsked RoundName.pscRound.name)) = true := by decide
theorem kind_y_asked : (OnBytes.Params.kindOf RoundName.pscY.name ==
    some (kindAsked RoundName.pscY.name)) = true := by decide
theorem kind_values_asked : (OnBytes.Params.kindOf RoundName.pscValues.name ==
    some (kindAsked RoundName.pscValues.name)) = true := by decide
theorem kind_batch_elems :
    (OnBytes.Params.kindOf RoundName.batSigma.name == some .elems) = true := by decide

/-- The rounds in the column bits, as the strict maker lays them. -/
theorem tapeS_plain (work : Nat) : ∀ (n : Nat) (u1 : List Fmt.RoundView) (l1 : List (List E × E))
    (rest : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    VarsRead (List.replicate n (Var.plain 3)) u1 l1 →
    (∀ r ∈ u1, r.drawn.poss = [] ∧ r.drawn.trits = []) → tapeS rest es = some t →
    tapeS (u1 ++ rest)
      (List.replicate n { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } ++
        es) = some (l1.map (fun y => rd (0, y.1, y.2)) ++ t)
  | 0, [], [], rest, es, t, _, _, ht => by simpa using ht
  | n + 1, r :: u1, (s, g) :: l1, rest, es, t, hv, hp, ht => by
    have hv' : Sent r ((Var.plain 3).d - 1) 1 s [g] ∧
        VarsRead (List.replicate n (Var.plain 3)) u1 l1 := hv
    have ih := tapeS_plain work n u1 l1 rest es t hv'.2
      (fun r' h' => hp r' (List.mem_cons_of_mem _ h')) ht
    have hr := roundS_of_sent hv'.1 (hp r List.mem_cons_self).1 (hp r List.mem_cons_self).2
      { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } rfl rfl rfl rfl
      name_round_ne kind_round_asked
    show tapeS (r :: (u1 ++ rest)) (_ :: (List.replicate n _ ++ es)) = _
    unfold tapeS
    rw [hr, ih]
    rfl
  | 0, [], _ :: _, _, _, _, hv, _, _ => hv.elim
  | 0, _ :: _, _, _, _, _, hv, _, _ => hv.elim
  | _ + 1, [], _, _, _, _, hv, _, _ => hv.elim
  | _ + 1, _ :: _, [], _, _, _, hv, _, _ => hv.elim

/-- In such rounds two scalars were sent each. -/
theorem plain_two : ∀ (n : Nat) (u1 : List Fmt.RoundView) (l1 : List (List E × E)),
    VarsRead (List.replicate n (Var.plain 3)) u1 l1 → ∀ y ∈ l1, y.1.length = 2
  | 0, [], [], _, y, hy => by cases hy
  | n + 1, r :: u1, (s, g) :: l1, hv, y, hy => by
    have hv' : Sent r ((Var.plain 3).d - 1) 1 s [g] ∧
        VarsRead (List.replicate n (Var.plain 3)) u1 l1 := hv
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hv'.1.2.1
    · exact plain_two n u1 l1 hv'.2 y hy
  | 0, [], _ :: _, hv, _, _ => hv.elim
  | 0, _ :: _, _, hv, _, _ => hv.elim
  | _ + 1, [], _, hv, _, _ => hv.elim
  | _ + 1, _ :: _, [], hv, _, _ => hv.elim

/-- The kind's maker of the tape returns on rounds that are read so. -/
theorem headMerge_tape (lk n work : Nat) (r₀ r1 rY rv : Fmt.RoundView) (u1 : List Fmt.RoundView) (x : Fmt.Ext)
    (mu eps c beta v : E) (l1 : List (List E × E))
    (hv0 : r₀.vals = []) (he0 : r₀.drawn.elems = [x]) (hp0 : r₀.drawn.poss = [])
    (ht0 : r₀.drawn.trits = [])
    (hq : ∀ r ∈ r1 :: (u1 ++ [rY, rv]), r.drawn.poss = [] ∧ r.drawn.trits = [])
    (s1 : Sent r1 1 1 [mu] [eps]) (hv1 : VarsRead (List.replicate lk (Var.plain 3)) u1 l1)
    (sY : Sent rY 1 1 [c] [beta]) (sV : Sent rv 1 0 [v] []) :
    mergeTapeE (r₀ :: r1 :: (u1 ++ [rY, rv])) (mergeEntries lk n work) =
      .ok (mergeTapeOf n (E.ofTriple x) mu eps 0 (l1.map fun y => (0, y.1, y.2)) 0 c beta 0 v) := by
  have q1 := hq r1 List.mem_cons_self
  have qY := hq rY (by simp)
  have qV := hq rv (by simp)
  have a1 := roundS_of_sent s1 q1.1 q1.2
    { name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } rfl rfl rfl rfl
    name_eps_ne kind_eps_asked
  have aY := roundS_of_sent sY qY.1 qY.2
    { name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 } rfl rfl rfl
    rfl name_y_ne kind_y_asked
  have aV := roundS_of_sent sV qV.1 qV.2 { name := RoundName.pscValues.name, msg := 24 } rfl rfl
    rfl rfl name_values_ne kind_values_asked
  have tEnd : tapeS [rY, rv]
      [{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
       { name := RoundName.pscValues.name, msg := 24 }] =
      some [⟨some RoundName.pscY.name, 1, 0, [c], [beta]⟩,
        ⟨some RoundName.pscValues.name, 0, 0, [v], []⟩] := by
    simp only [tapeS, aY, aV]
  have tMid := tapeS_plain work lk u1 l1 [rY, rv] _ _ hv1
    (fun r hr => hq r (List.mem_cons_of_mem _ (List.mem_append_left _ hr))) tEnd
  have tAll : tapeS (r1 :: (u1 ++ [rY, rv]))
      ({ name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } ::
        (List.replicate lk
            { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 } ++
          [{ name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 },
           { name := RoundName.pscValues.name, msg := 24 }])) =
      some (⟨some RoundName.pscEpsilon.name, 0, 0, [mu], [eps]⟩ ::
        (l1.map (fun y => rd (0, y.1, y.2)) ++
          [⟨some RoundName.pscY.name, 1, 0, [c], [beta]⟩,
            ⟨some RoundName.pscValues.name, 0, 0, [v], []⟩])) := by
    unfold tapeS
    rw [a1, tMid]
  have b1 : batchEntryB
      { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } = true := by
    show (OnBytes.Params.kindOf RoundName.batSigma.name == some .elems && (1 : Nat) == 1 &&
      (0 : Nat) == 0 && (0 : Nat) == 0) = true
    rw [kind_batch_elems]
    rfl
  have b2 : batchRoundB
      { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } r₀ = true := by
    simp [batchRoundB, hv0, he0, hp0, ht0]
  have fl : flatOf r₀
      (some { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n }) =
      ⟨some RoundName.batSigma.name, 0, n, [], [E.ofTriple x]⟩ := by
    unfold flatOf
    rw [hv0, he0]
    rfl
  unfold mergeEntries mergeTapeE
  simp only [need, named, b1, b2, tAll, fl, bind, Except.bind, pure, Except.pure, if_true]
  unfold mergeTapeOf
  rw [List.map_map]
  rfl

/-! ## The flat text of the merge, with its tests on the claims -/

theorem headMerge_flatEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (F G : Fork)
    (x mu eps c beta v T fvp : E) (w0 wY wV : Nat) (xs : List (Nat × List E × E))
    (h1 : cl.size ≠ 0) (h2 : cl.size ≤ 4096) (h3 : sv.size = cl.size)
    (h4 : ∀ q ∈ cl, q.ui < lay.U.size ∧ claimFits lay q = true) (hxl : xs.length = lay.lk)
    (hx : ∀ y ∈ xs, y.2.1.length = 2)
    (hT : F.publicPart (wsForkStart sv (powers x sv.size)) = some T)
    (hG : ({ F with next := F.next + 1 + 2 * lay.lk + 1 + 1 } : Fork).hideRun
      (F.next + 1 + 2 * lay.lk + 1) #[v] beta = some G)
    (hsh : G.shown (F.next + 1 + 2 * lay.lk + 1) = some fvp) :
    ∃ wo : WsForkOut,
      flatForkEnd lay cl sv F (mergeTapeOf sv.size x mu eps w0 xs wY c beta wV v) =
        some (wo, G, []) ∧
      wo.p = endP (beginP sv x T mu eps F.next) (xs.map plainRnd) (Weight.atZero 2, [c], beta) ∧
      wo.sFv = F.next + 1 + 2 * lay.lk + 1 ∧ wo.rm.toList = xs.map (·.2.2) ∧ wo.fvp = fvp ∧
      wo.beta = beta ∧
      wo.recs = (cl.zip (powers x sv.size)).toList.map fun y =>
        wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)) := by
  have e0 : cl.isEmpty = false :=
    Bool.eq_false_iff.mpr (Array.isEmpty_iff_size_eq_zero.not.mpr h1)
  have e1 : (!cl.isEmpty && decide (cl.size ≤ 4096) && sv.size == cl.size) = true := by
    simp [e0, h2, h3]
  have e2 : (cl.all fun q => decide (q.ui < lay.U.size)) = true :=
    Array.all_eq_true_iff_forall_mem.mpr fun q hq => by simpa using (h4 q hq).1
  have e3 : (cl.all fun q => (OnBytes.Model.wsClaimShape lay q).isOk) = true :=
    Array.all_eq_true_iff_forall_mem.mpr fun q hq => by
      rw [← claimFits_eq]
      exact (h4 q hq).2
  have hm := headMerge_merge lay.lk sv F G x mu eps c beta v T fvp w0 wY wV xs (by omega) hxl hx hT
    hG hsh
  unfold flatForkEnd
  refine ⟨_, bind_eq (must_eq e1 _ _) (bind_eq (must_eq e2 _ _) (bind_eq (must_eq e3 _ _)
    (bind_eq hm rfl))), rfl, rfl, ?_, rfl, ?_, rfl⟩
  · show (((Array.emptyWithCapacity lay.lk : Array E).toList ++ xs.map (·.2.2)).toArray).toList = _
    simp
  · show (((runP (beginP sv x T mu eps F.next) (xs.map plainRnd)).r.push beta).back?).getD zeroE = _
    simp

/-! ## Lists -/

theorem plain_weights : ∀ l1 : List (List E × E),
    ((l1.map fun y => ((0 : Nat), y.1, y.2)).map plainRnd).map (·.1) =
      (List.replicate l1.length (Var.plain 3)).map Var.weight
  | [] => rfl
  | y :: l => by
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    rw [plain_weights l]
    rfl

theorem plain_sent : ∀ l1 : List (List E × E),
    ((l1.map fun y => ((0 : Nat), y.1, y.2)).map plainRnd).map (fun m => (m.2.1, m.2.2)) = l1
  | [] => rfl
  | y :: l => by
    simp only [List.map_cons]
    rw [plain_sent l]
    rfl

theorem plain_drawn : ∀ l1 : List (List E × E),
    (l1.map fun y => ((0 : Nat), y.1, y.2)).map (·.2.2) = l1.map (·.2)
  | [] => rfl
  | y :: l => by
    simp only [List.map_cons]
    rw [plain_drawn l]

theorem lensT_plain (c beta : E) : ∀ (l1 : List (List E × E)), (∀ y ∈ l1, y.1.length = 2) →
    LensT (List.replicate l1.length (Var.plain 3) ++ [Var.point zeroE (1 + 1)])
      (l1 ++ [([c], beta)])
  | [], _ => ⟨rfl, trivial⟩
  | y :: l, h => by
    refine ⟨?_, lensT_plain c beta l fun z hz => h z (List.mem_cons_of_mem _ hz)⟩
    show y.1.length + 1 = 3
    rw [h y List.mem_cons_self]

theorem foldl_plain_slots : ∀ (n a : Nat),
    (List.replicate n (Var.plain 3)).foldl (fun m v => m + (v.d - 1)) a = a + 2 * n
  | 0, a => rfl
  | n + 1, a => by
    rw [List.replicate_succ, List.foldl_cons, foldl_plain_slots n]
    show a + (3 - 1) + 2 * n = a + 2 * (n + 1)
    omega

theorem ownSlots_headMerge (lk : Nat) :
    ownSlots (List.replicate lk (Var.plain 3) ++ [Var.point zeroE (1 + 1)]) = 2 * lk + 2 := by
  unfold ownSlots
  rw [List.foldl_append, foldl_plain_slots]
  show 1 + 2 * lk + (1 + 1 - 1) = 2 * lk + 2
  omega

/-! ## The statement -/

theorem headMergeHears : HeadMergeHears := by
  intro lay cl sv F G work r₀ rs x h h1 h2 h3 h4 hS hv0 he0 hp0 ht0 hrs hh
  obtain ⟨_, T, R, hT, hR, hhe, hG⟩ := hear_spec hh
  obtain ⟨r1, used, rv, front, ers, s1, hf, hvr, sV⟩ :=
    readAll_spec (lead := 0) (vs := List.replicate lay.lk (Var.plain 3)) (e := ⟨1, 1⟩) hR
  obtain ⟨u1, u2, l1, l2, eu, el, hv1, hv2⟩ := VarsRead.split hvr
  obtain ⟨rY, sY, beta, eu2, el2, sY1⟩ := VarsRead.one hv2
  have hfr : front = [] := List.eq_nil_of_length_eq_zero hf
  subst hfr eu2 el2 eu
  obtain ⟨c, rfl⟩ : ∃ c, sY = [c] := List.length_eq_one_iff.1 sY1.2.1
  obtain ⟨v, hv⟩ : ∃ v, R.values = [v] := List.length_eq_one_iff.1 sV.2.1
  rw [hv] at sV
  have hlen : l1.length = lay.lk := by
    have a := (VarsRead.length hv1).2
    rwa [List.length_replicate] at a
  have ers' : rs = r1 :: (u1 ++ [rY, rv]) := by
    rw [ers, List.append_assoc]
    rfl
  have htwo := plain_two lay.lk u1 l1 hv1
  have htape := headMerge_tape lay.lk cl.size work r₀ r1 rY rv u1 x R.mu R.eps c beta v l1 hv0 he0
    hp0 ht0 (by rw [← ers']; exact hrs) s1 hv1 sY1 sV
  have hall : (headMergeShape lay.lk).all =
      List.replicate lay.lk (Var.plain 3) ++ [Var.point zeroE (1 + 1)] := rfl
  have hlast : (R.rounds.map (·.2)).getLastD zeroE = beta := by
    rw [el]
    simp
  have hslot : F.next + ownSlots (headMergeShape lay.lk).all = F.next + 1 + 2 * lay.lk + 1 := by
    rw [hall, ownSlots_headMerge]
    omega
  have hG' : ({ F with next := F.next + 1 + 2 * lay.lk + 1 + 1 } : Fork).hideRun
      (F.next + 1 + 2 * lay.lk + 1) #[v] beta = some G := by
    rw [hslot, hv, hlast] at hG
    exact hG
  obtain ⟨hsame, _, hrun, _⟩ := OnBytes.PscRun.hideRun_ok
    ({ F with next := F.next + 1 + 2 * lay.lk + 1 + 1 } : Fork) G _ _ _ hS hG'
  have h0 := hrun 0 (by simp)
  have hsh : G.shown (F.next + 1 + 2 * lay.lk + 1) =
      some (G.vp.getD (F.next + 1 + 2 * lay.lk + 1) zeroE) :=
    shown_returns (by rw [hsame.ns]; exact h0.1) h0.2.2.1
  obtain ⟨wo, hfl, wp, wsf, wrm, wfv, wbe, wre⟩ := headMerge_flatEnd lay cl sv F G (E.ofTriple x)
    R.mu R.eps c beta v T _ 0 0 0 (l1.map fun y => ((0 : Nat), y.1, y.2)) h1 h2 h3 h4
    (by rw [List.length_map, hlen])
    (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact htwo z hz) hT hG' hsh
  have hheld : ∀ m ∈ (l1.map fun y => ((0 : Nat), y.1, y.2)).map plainRnd ++
      [((Weight.atZero 2, [c], beta) : Rnd)], Held m.1 := by
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨z, _, rfl⟩ := List.mem_map.1 hm
      exact held_plain_three
    · rw [List.mem_singleton.1 hm]
      exact held_atZero 2 (by omega)
  have hE := endP_ended T R.mu R.eps F.next (wsForkStart sv (powers (E.ofTriple x) sv.size))
    ((l1.map fun y => ((0 : Nat), y.1, y.2)).map plainRnd) (Weight.atZero 2, [c], beta) 1 rfl hheld
  rw [plain_weights, plain_sent, hlen] at hE
  have hL := lensT_plain c beta l1 htwo
  rw [hlen] at hL
  have hSL := flatEnded _ _ _ _ _ _ _ _ _ _ _ hE hL
  have hEq : h = heardAs (wsForkStart sv (powers (E.ofTriple x) sv.size)) T R.mu R.eps F.next
      (List.replicate lay.lk (Var.plain 3)) l1 1 [c] beta := by
    rw [hhe, el]
    unfold heardAs
    simp only [List.map_append, List.map_cons, List.map_nil]
    rfl
  obtain ⟨f1, f2, f3, f4⟩ := endP_row_ready (beginP sv (E.ofTriple x) T R.mu R.eps F.next)
    ((l1.map fun y => ((0 : Nat), y.1, y.2)).map plainRnd) (Weight.atZero 2, [c], beta) rfl rfl rfl
  refine ⟨_, wo, by rw [ers']; exact htape, hear_of_flat (by rw [← h3]; exact hfl), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, wre⟩
  · rw [wp, hEq]
    exact hSL
  · rw [wp]
    exact f2
  · rw [wp]
    exact f1
  · rw [wp]
    exact f3
  · rw [wp]
    exact f4
  · rw [wsf, hhe]
    exact hslot.symm
  · rw [wrm, hhe, plain_drawn]
    show l1.map (·.2) = (R.rounds.map (·.2)).take lay.lk
    rw [el, List.map_append, List.take_left' (by rw [List.length_map, hlen])]
  · rw [wbe, hhe]
    exact hlast.symm
  · rw [wfv, hhe]
    show G.shown (F.next + ownSlots (headMergeShape lay.lk).all) = _
    rw [hslot]
    exact hsh

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headMerge_tape
#print axioms ProofFile.Honest.K11.headMergeHears
