-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Grows.lean: A YES OF THE PROXIMITY TEST (THE KIND K12) ONLY GROWS THE STATEMENT, AND MARKS THE GROUP UNDER TEST. General in the place. Statements and proofs.
OBJECT. The decision of `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/JoinGuarded.lean) and of `rangesTest laid back N` (Johnson/Desc/Key/Ranges.lean), against `Grows` (Johnson/Desc/Grows.lean).
USER. Johnson/RunOne/Law/RngAnyCl.lean (seat_grows_cl), and through it RngAtKeyD.lean (keyD_grows).
LETTERS. The place is free. Premises: early, answers = 1, the block's yes.

The setting. "A statement only grows" (`Grows`: Johnson/Desc/Grows.lean: the same codes; no group and no oracle message is dropped or changes its number; a group keeps its codes and members and a mark inRun is not taken back; a message keeps its shape
and the groups that it names, and a mark sampled is not taken back) is what the law on the chains' ends (Johnson/Desc/ChainEndCovered.lean) asks of every block, one step a kind: in that law's words `Keeps.Decides (GrowsBy st) b`, which unfolds to: for all s rs gs s', b.decide s rs gs = .ok s' → Grows (st s) (st s').
The kind's own files have what a yes leaves (OutK, OutK2): codes; every older group; every older message that is no member and not the first mask, to the letter; shapes of all. They say nothing of a member's or the mask's marks.

What is said.
  `stage_mask`: THE ONE NEW FACT: behind a stage but the last, the message that the record named as the stage's mask is what it was with the mark "spent as a mask" set. (stage_st, Johnson/Desc/K12/Law/OutK2.lean, proves it on its way and keeps of it "there is a message, spent": the first lines of this file's proof call the
    same lemmas in the same order as that proof.)
  `stages_go`: the stages from a stage on: every older group and message has grown. No recursion in this file: the first stage, then StagesSt (OutK2.lean) for what follows (the later stages' masks are messages that have come since).
  `k12_grows_of`: for parts X that are `Like` the kind's and whose base case leaves `BaseSt`: where proximityTestKind X p's decide returns tE at t0 (early = true; answers = 1): Grows t0.st tE.st, AND the group under test is there, marked, without an open row, and else as it was.
  `k12_grows`, `k12_grows_joined`: of the variant proximityTestKind guardedProximityTestParts (Johnson/Desc/K12/JoinGuarded.lean) and of the kind's own parts (proximityTestKind proximityTestParts).
  `seat_grows`: OF THE BLOCK AT A KEY FILE's RANGES' TEST (rangesTest), AT ANY STATE: for a reading st of the statement off the state such that the seat's first half lays st s and its second half writes the record's statement: the frame's `Decides (GrowsBy st)`, unfolded.
What is asked, by name. he, ha: two numbers of the place (that block's test on the plan asks them). hin, hout: of the seat's two halves: each is an unfolding at a given seat.
Limits. `Grows` says nothing on rows, pads, ledgers or the mark "spent as a mask". Cl := Unit, as the kind's laws are. The frame's own names (Johnson/Desc/FoldKeeps.lean: Decides; Johnson/Desc/ChainEndCovered.lean: GrowsBy) are not imported: the statements here are their unfolding, to be wrapped
by whoever needs them in that form. A block that says no to all meets every statement here. Nothing on soundness.

-/
import Johnson.Desc.Grows
import Johnson.Desc.K12.Law.OutK2
import Johnson.RunOne.Law.RngAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Grows
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok)

/-- Every older group and every older oracle message has grown: `Grows` but for the codes. -/
def GO (T T' : Statement) : Prop :=
  (∀ (i : Nat) G, T.groups[i]? = some G → ∃ G', T'.groups[i]? = some G' ∧ GroupGrows G G') ∧
    ∀ (i : Nat) x, T.oracles[i]? = some x → ∃ x', T'.oracles[i]? = some x' ∧ OracleGrows x x'

theorem lt_of_some {α : Type} {xs : Array α} {i : Nat} {a : α} (h : xs[i]? = some a) : i < xs.size :=
  (Array.getElem?_eq_some_iff.1 h).1

/-- **The one new fact**: behind a stage but the last, the stage's mask is what it was, spent. -/
theorem stage_mask (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cutF cutS : List Fmt.DeclaredRound) (t t1 t2 t3 : T12)
    (rsF rsS : List Fmt.RoundView) (gsF gsS : Gs) (hlen : rsS.length ≤ 2)
    (f1 : (foldJ p j cur cutF).decide t rsF gsF = .ok t1)
    (f2 : (switchJ p j cur nxt last cutS).decide t1 rsS gsS = .ok t2)
    (f3 : (behindJ p (j + 1) nxt cutS).decide t2 [] [] = .ok t3)
    {id : ℕ} {x : OnBytes.Oracle} (hmk : t.mask = some id) (hx : t.st.oracles[id]? = some x) :
    t3.st.oracles[id]? = some { x with spentAsMask := true } := by
  obtain ⟨row, L, c, n, id', d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cutF t t1 rsF gsF f1
  obtain ⟨rows', gp, nx, out, row', L', th, D, hp, hd, _⟩ :=
    switch_did p he ha j cur nxt last cutS _ t2 t3 rsS gsS hlen f2 f3
  obtain ⟨rfl, rfl⟩ : rows = rows' ∧ d'.st.groups.size = gp := by
    cases hp
    exact ⟨rfl, rfl⟩
  have hthere := spendP_there hsp
  have hd' := spendP_form hsp
  obtain ⟨e1, e2⟩ : id' = id ∧ d1 = ⟨t.st, t.book, t.roots, keyed p cutF gsF, ()⟩ := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨Option.some.inj (h1.symm.trans hmk), h2⟩
    · rw [hmk] at h1
      cases h1
  subst e1
  subst e2
  have hG : D.G.members = #[] := by
    have hg := hd.group
    rw [ledgerShut_groups] at hg
    have hg' : (d'.st.groups.push { code := n.1, maskCode := n.2 })[d'.st.groups.size]? = some D.G := hg
    rw [Array.getElem?_push_size] at hg'
    rw [← Option.some.inj hg']
  obtain ⟨_, c2⟩ := did_oracles hd hG
  have hS : (Ground.withGroup d'.st n.1 n.2).oracles = d'.st.oracles := rfl
  dsimp only at c2
  rw [hS] at c2
  have hsz : d'.st.oracles.size = t.st.oracles.size := by
    rw [hd']
    show (t.st.oracles.modify id' _).size = _
    rw [Array.size_modify]
  rw [c2 id' (by rw [hsz]; exact hthere), hd']
  show (t.st.oracles.modify id' _)[id']? = _
  rw [Array.getElem?_modify, if_pos rfl, hx]
  rfl

/-- The stages from a stage on: every older group and message has grown. -/
theorem stages_go (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (he : p.early = true) (ha : p.answers = 1) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE) : GO t.st tE.st := by
  cases rest with
  | nil =>
    rw [stagesFrom_last] at h
    obtain ⟨star, _, _, h3⟩ := hB _ _ _ _ _ _ _ h
    rw [h3]
    exact (grows_modOracle t.st star (fun x => { x with spentAsMask := true })
      fun _ => ⟨rfl, id, fun _ k => k⟩).2
  | cons nxt rest =>
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have F1 := hX.fold _ _ _ _ _ _ _ f1
    have F2 := hX.switch _ _ _ _ _ _ _ _ _ f2
    have F3 := hX.behind _ _ _ _ _ f3
    obtain ⟨a1, a2, _, a4, a5, _, _, a8⟩ :=
      stage_st p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen F1 F2 F3
    have ih := stages_st X p hX hB he ha rest (j + 1) nxt _ t3 tE _ _ f5
    refine ⟨fun i G hG => ?_, fun i x hx => ?_⟩
    · have hi := lt_of_some hG
      exact ⟨G, by rw [ih.groupsOld i (by omega), a2 i hi]; exact hG, GroupGrows.refl G⟩
    · have hi := lt_of_some hx
      have hne : t3.mask ≠ some i := by
        rw [a8]
        intro e
        have := Option.some.inj e
        omega
      by_cases hm : t.mask = some i
      · exact ⟨{ x with spentAsMask := true }, by
          rw [ih.oraclesOld i (by omega) hne]
          exact stage_mask p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen F1 F2 F3 hm hx,
          rfl, id, fun _ k => k⟩
      · exact ⟨x, by rw [ih.oraclesOld i (by omega) hne, a5 i hi hm]; exact hx, OracleGrows.refl x⟩

/-- **A yes of the proximity test only grows the statement, and marks the group under test.** -/
theorem k12_grows_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) :
    Grows t0.st tE.st ∧ ∃ G, t0.st.groups[t0.g]? = some G ∧
      tE.st.groups[t0.g]? = some { G with inRun := true, rows := #[] } := by
  have hc := (k12_out_of X p hX he ha t0 tE rs gs h).codes
  obtain ⟨G2, k2⟩ := k12_out2_of X p hX hB he ha t0 tE rs gs h
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have g1 := grows_begun tF.st tF.g G
  have g2 := stages_go X p hX hB he ha rest 0 first _ _ tE _ _ hst
  exact ⟨g1.trans ⟨hc.trans g1.1.symm, g2.1, g2.2⟩, G2, k2.was, k2.begunG⟩

/-- Of the variant proximityTestKind guardedProximityTestParts. -/
theorem k12_grows (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    Grows t0.st tE.st ∧ ∃ G, t0.st.groups[t0.g]? = some G ∧
      tE.st.groups[t0.g]? = some { G with inRun := true, rows := #[] } :=
  k12_grows_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha t0 tE rs gs h

/-- Of the kind's own parts. -/
theorem k12_grows_joined (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind K12.proximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    Grows t0.st tE.st ∧ ∃ G, t0.st.groups[t0.g]? = some G ∧
      tE.st.groups[t0.g]? = some { G with inRun := true, rows := #[] } :=
  k12_grows_of K12.proximityTestParts p (like_joined p) (fun j cur cut t t' rs gs h => baseJ_st p j cur cut t t' rs gs h)
    he ha t0 tE rs gs h

open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked in
/-- **Of the block at a key file's ranges' test, at any state**: the frame's `Decides (GrowsBy st)`, unfolded. -/
theorem seat_grows {σ : Type} (st : σ → Statement) {laid : σ → Except String Key.RangesLaid}
    {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}
    (hin : ∀ s l, laid s = .ok l → l.d.st = st s) (hout : ∀ s t s', back s t = .ok s' → st s' = t.st)
    (hp : (rangesTest (Cl := Unit) laid back N).planOk = true) :
    ∀ s rs gs s', (rangesTest (Cl := Unit) laid back N).decide s rs gs = .ok s' → Grows (st s) (st s') := by
  intro s rs gs s' h
  obtain ⟨_, he, ha, _, _⟩ := planOk_ok hp
  obtain ⟨t0, tE, h1, _, hd, hbk⟩ := decide_ok h
  unfold rangesRecord at h1
  obtain ⟨l, hl, rfl⟩ := mapE_ok h1
  have g := (k12_grows (rangesParams N) he ha _ tE rs gs hd).1
  rw [hout s tE s' hbk, ← hin s l hl]
  exact g

end Johnson.RunOne.Law.K12Grows

#print axioms Johnson.RunOne.Law.K12Grows.stage_mask
#print axioms Johnson.RunOne.Law.K12Grows.stages_go
#print axioms Johnson.RunOne.Law.K12Grows.k12_grows_of
#print axioms Johnson.RunOne.Law.K12Grows.k12_grows
#print axioms Johnson.RunOne.Law.K12Grows.k12_grows_joined
#print axioms Johnson.RunOne.Law.K12Grows.seat_grows
