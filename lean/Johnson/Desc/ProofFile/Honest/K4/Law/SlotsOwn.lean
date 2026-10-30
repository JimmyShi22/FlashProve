-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SlotsOwn.lean: CONDITIONAL.

Not shown here. No property is claimed. THAT THE PREMISES CAN BE MET: no example is known. WHICH
WORLD IS MEANT: the own slots of two of the seven sumchecks are laid late: those of the token
sumcheck on the row products by the run "front", the merge's by the run "back". The statements on
these two speak of the ledger that the run leaves and of every later one. Of an earlier ledger's
world nothing is said; in the ledger from which the run starts these slots are not filled
(`front_free`, `back_free`: no statement calls these two: they stand for this sentence alone; so
does `hidingCoin_there` for the one on the coin below). NOT HERE: the own slots of the lookup's
sumcheck over the leaves, which "front" lays too. Nor any slot of a value that is sent
(Law/SlotsTrue.lean). Law/OwnAtStand.lean spends five of the seven, Law/StackAtStand.lean the two on
the second token sumcheck and on the batched sumcheck. That the step of K4's member accepts is a
premise. Nothing on the law of any coin. Nothing on soundness, on completeness or on any other
property.

THE PUBLIC TEST `k4Fits` (Honest/K4/Part.lean) is among the premises by name, and is not in force at
the stand: the field fits of `K4Seated` (Law/Seated.lean) says that the test accepts at every list
of challenges that the rounds in front can sample and at every valid input. That it accepts at the
stand's own challenges and input follows from it only with two clauses of `Thr`
(Honest/Thread/Thr.lean), which a stand does not hold. No statement here calls that field: with it
struck from the premises each stands by the same proof: they hold at shapes that do not fit too.
WHERE A MAKER RETURNS NOTHING: no statement here asks that a maker returns: the slot is worth the
coin there too. It is a coin, not the 0 that stands in where a list is too short: below the number
of own slots `hidingCoin cp i` reads a member of the part's first run of coins (`hidingCoin_there`).

Words. K4: the sub-protocol of the feed-forward layers' own rounds. Ledger: `Fork`
(OnBytes/Model/). World of a ledger: `Fork.worldOf` (OnBytes/Model/HideLaws.lean). The hearing:
`hearFl`; the runs "front" and "back": `formsFrontWith`, `formsBack` (all three:
OnBytes/Desc/First/K4/Plain.lean). A stand, and the book: Law/SlotsTrue.lean. `hidingCoin`
(Honest/SumLaw/Statement.lean): the library's name for the coin that the masked sumcheck's part
spends for one coefficient of the polynomial that the format calls the hiding polynomial. "Later" is
`OnBytes.PscRun.Later`; `run_under` and `level_own` ask the lesser `Fo.Later`, as the library's
statements on the hearing give it (Law/SaidKit.lean, at `slot_value`, says what leads from one to
the other).

What is here. Each of K4's seven masked sumchecks has slots of its own: one for each such
coefficient. Behind the step of K4's member on what the honest row has played from a stand: in the
world of a ledger that is late enough, on the mask row that is read off the witness, own slot number
i of a sumcheck is worth `hidingCoin cp i`, cp what the part is handed of the coins that the book
lends the row. For five of the seven that is, letter for letter, the premise hs of the five
statements of Law/FlatTops.lean. Definitions, and statements with their proofs.

THE PREMISES. `K4Stand` (Law/SlotsTrue.lean), all of whose fields are read: among them the tie of
the mask row to the coins at the stand (`K4MaskTieAt`, Law/ScriptAt.lean). c: what the book lends
the row (`lendRow`, Honest/Frame.lean). `SumAt`: the row's part of that number is the masked
sumcheck's part at the job, and it is handed cp. Fj, F0: any ledger from which the verifier's
function for that sumcheck returns what the hearing holds of it (`o.H.wpl`, `o.H.tV`, `o.hd`, `o2`,
`o.wo`): of that return the next slot of the ledger in front alone is read, so its other arguments
are free.

  1  `OwnUnder G j n`, `run_under`, `entries_count`, `level_own`, `tsc_len`   n slots from j on are
     filled, show 0 and have the factor -1; the making of a sumcheck's own claim lays just that
  2  `HeardOwn P hp g o G`, `hear_own`, `front_own`, `back_own`, `front_free`, `back_free`   free of
     the honest side's frame: one field for each of the five sumchecks whose own slots the hearing
     fills; where the two late runs of slots begin and how long they are; a return of the hearing
     gives it; what "front" and "back" lay, and that they find these slots not filled
  3  `own_shapes`, `row_own_nums`, `row_bounds`, `OwnStarts`, `own_starts`, `row_jobs`   public: how
     many own slots each shape has; the coins in front of the merge's part and in the whole row;
     slot = n + coin at the seven runs of own slots; the seven parts in the row
  4  `SumAt`, `sumAt_some`, `hidingCoin_there`, `hidingCoin_seated`, `own_field`, `worldBehind`,
     `own_ground`   a part of the lent row and its coins; one statement that is general in the part;
     the world; what every one of the seven begins with
  5  `squares_hs`, `rows_hs`, `terms_hs`, `stack_hs`, `gated_hs`, `gated2_hs`, `merge_hs`   **the
     seven**
  6  two examples: the two on the second token sumcheck and on the batched sumcheck, in the form in
     which the general statements on the masked sumcheck's part ask them
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatTops
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts
import Johnson.Desc.First.K4.LedgerKeeps
import Johnson.Road.K4.HearSlotsEnd
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.SlotsOwn
open OnBytes (zeroE oneE subE addE mulE)
open OnBytes.Psc (Weight hidingEntries)
open OnBytes.Model (Reading Aff Fork World Level Tsc WsClaim)
open OnBytes.Model.Layer (HPlan2 Own nEndT)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.PscRun (Sized Filled Later hideRun_ok)
open OnBytes.Desc.First.K4 (Par hearFl engFl k0 hear_slots hear_end_first hear_end_later
  flatForkEnd_slots k4Slots hearStack_tape hearTerms_calls formsFrontWith formsBack
  formsFrontWith_some formsBack_some)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.P1 (levelIn_heard tscIn_heard levelRec levelMs levelY levelWs tscWs plainWs
  walk_length tsc_walk tsc_world pscRow_spec endP_spec)
open OnBytes.Road.K4 (own_ledG)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ)
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open ProofFile.Honest.SumLaw

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-! ## 1 What the making of a sumcheck's own claim lays -/

/-- **The n slots from j on are filled in the ledger G; each shows 0 and has the factor -1.** -/
def OwnUnder (G : Fork) (j n : Nat) : Prop :=
  ∀ e, e < n → Under G (j + e) zeroE (subE zeroE oneE)

/-- A later ledger holds the same. -/
theorem OwnUnder.later {G H : Fork} {j n : Nat} (h : OwnUnder G j n) (hL : Later G H) :
    OwnUnder H j n := fun e he => (h e he).later hL

/-- **Where n zeros are laid with the factor -1 from slot j on**, from a ledger whose arrays have
their sizes: so it is in every later ledger. -/
theorem run_under {F G H : Fork} {j n : Nat} (hF : Sized F)
    (h : F.hideRun j (Array.replicate n zeroE) (subE zeroE oneE) = some G) (hL : Fo.Later G H) :
    OwnUnder H j n := by
  intro e he
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G j _ _ hF h
  have q := hin e (by rw [Array.size_replicate]; exact he)
  have r := hL.keep (j + e) q.2.2.1
  have hz : (Array.replicate n zeroE).getD e zeroE = zeroE := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  exact ⟨r.1, by rw [r.2.1, q.2.2.2.1, hz], by rw [r.2.2, q.2.2.2.2]⟩

/-- The library's count of a sumcheck's own slots, where each variable has three coefficients and
the further variable dY + 1. -/
theorem entries_count (ws : List Weight) (h : ∀ w ∈ ws, w.d = 3) (dY : Nat) :
    hidingEntries (ws ++ [Weight.atZero (dY + 1)]) = ownOf 0 ws.length dY := by
  have s : ∀ l : List Weight, (∀ w ∈ l, w.d = 3) →
      (l.map fun w => w.d - 1).sum = 2 * l.length := by
    intro l
    induction l with
    | nil =>
      intro _
      rfl
    | cons a l ih =>
      intro hl
      rw [List.map_cons, List.sum_cons, hl a (by simp), ih fun w hw => hl w (by simp [hw]),
        List.length_cons]
      omega
  unfold hidingEntries ownOf
  rw [List.map_append, List.sum_append, s ws h]
  show 1 + (2 * ws.length + (dY + 1 - 1 + 0)) = _
  omega

/-- **A product level lays its own slots itself**: they begin at the next slot of the ledger in
front and end where its left end value's slot stands. -/
theorem level_own {mu : Nat} {rho : Array OnBytes.E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn mu rho C order F t = some (L, G, u)) (Hl : Fork) (hL : Fo.Later G Hl) :
    F.next + ownOf 0 mu 2 = L.sL ∧ OwnUnder Hl F.next (ownOf 0 mu 2) := by
  obtain ⟨hom, _, _, a1, hy, hheld, _, hvars, hr, _, _, _, hfirst, _, hsL, _, _, _, v, G1, _, hG1,
    _, hG⟩ := levelIn_heard h
  have hv' : (levelRec mu rho C order F t).vars.toList =
      (levelMs mu rho order t ++ [levelY mu t]).map (·.1) := by
    rw [hvars, List.map_append, a1]
    simp [hy]
  have hwl : (levelRec mu rho C order F t).walk.1.length = ownOf 0 mu 2 := by
    rw [walk_length (by simp) hv' hr hheld, ← hv', hvars]
    refine (entries_count _ (fun w hw => ?_) 2).trans ?_
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
      rfl
    · rw [levelWs, List.length_map, hom]
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ G1 L.sL v _ hF' hG1
  rw [hfirst, hwl] at hG
  refine ⟨?_, run_under hS1 hG hL⟩
  rw [hsL]
  unfold ownOf
  omega

/-- How many own slots a token sumcheck's state counts. -/
theorem tsc_len {P : Array OnBytes.E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) : o.p.walk.1.length = ownOf 0 lt dY := by
  have hlt := (tscIn_heard h).1
  rw [tsc_walk h]
  refine (entries_count _ (fun w hw => ?_) dY).trans ?_
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
    rfl
  · rw [tscWs, List.length_map, List.length_take, Array.length_toList, Nat.min_eq_left hlt]

/-! ## 2 The seven runs of own slots, free of the honest side's frame -/

/-- **What the ledger G holds under the own slots of five sumchecks, and where the two late runs of
own slots lie.** A level and the batched sumcheck have no name for their first own slot: it is the j
from which as many slots as the sumcheck has of its own reach to its first end value's slot. -/
structure HeardOwn (P : OnBytes.Model.Layer.Pub) (hp : HPlan2) (g : Nat) (o : Own) (G : Fork) :
    Prop where
  /-- the ledger's arrays have their sizes -/
  sized : Sized G
  /-- the squares' level -/
  sq : ∀ j, j + ownOf 0 P.rd.muV 2 = o.H.wpl.sL → OwnUnder G j (ownOf 0 P.rd.muV 2)
  /-- the second token sumcheck -/
  terms : ∀ tT, o.H.tT = some tT → OwnUnder G (tT.sCl + 1) (ownOf 0 P.y.h.lt 1)
  /-- the batched sumcheck -/
  stack : ∀ j, j + ownOf 0 hp.lamS 2 = o.K.sA0 → OwnUnder G j (ownOf 0 hp.lamS 2)
  /-- the first gated level -/
  lv1 : ∀ j, j + ownOf 0 P.rd.muH 2 = o.hd.sL → OwnUnder G j (ownOf 0 P.rd.muH 2)
  /-- the second gated level -/
  lv2 : ∀ o2, o.hd2 = some o2 → ∀ j, j + ownOf 0 P.rd.muH2 2 = o2.sL →
    OwnUnder G j (ownOf 0 P.rd.muH2 2)
  /-- the token sumcheck on the row products: its first own slot, and how many "front" lays -/
  pV : o.H.tV.p.first = o.H.tV.sCl + 1
  wV : o.H.tV.p.walk.1.length = ownOf 0 P.y.h.lt 2
  /-- the merge: its first own slot, and how many "back" lays -/
  pM : ∀ o2, o.hd2 = some o2 →
    o.wo.p.first = o2.sL + 2 + (if (g == 0) = true then 1 else 0)
  wM : o.wo.p.walk.1.length = ownOf 0 P.wsLay.lk 1

/-- **A return of the hearing gives it**, from a ledger whose arrays have their sizes. -/
theorem hear_own {P : OnBytes.Model.Layer.Pub} {hp : HPlan2} {g : Nat}
    {fo : OnBytes.Model.Forest.Heard} {F G : Fork} {t u : Tape} {o : Own} (hF : Sized F)
    (h : hearFl P hp g fo F t = some (o, G, u)) : HeardOwn P hp g o G := by
  have h' : OnBytes.Desc.First.K4.hear engFl P hp g fo F t = some (o, G, u) := h
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hF h'
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨v2, c2⟩ := L.c2
  obtain ⟨v5, c5⟩ := L.c5
  obtain ⟨cl, c7⟩ := L.c7
  obtain ⟨_, _, _, a4, a5, _, _, _, _, _, _, _, hd2', h2', a13⟩ := hear_slots Reading.gl hF h'
  -- the second token sumcheck
  obtain ⟨u1, _, hT⟩ := L.nt
  obtain ⟨t0, K1, w1, row, p', cT, _, cR, hH⟩ := hearTerms_calls hT
  obtain ⟨_, sK1, tP, _⟩ := tsc_world Reading.gl (fun _ => 0) (fun _ _ _ => 0) L.s1 cT
  have hsCl : t0.sCl = G1.next := (tscIn_heard cT).2.2.2.2.2.2.2.2.2.2.1
  have hR := (pscRow_spec cR).2.2
  rw [tsc_len cT] at hR
  -- the batched sumcheck
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1', wY, wV, C, Gs, ms, yy, q, _, _, _, _, _, _,
    hyy, hq, a1, hheld, _, _, hsA0, _, _, _, _, hGs, _, hG3⟩ := hearStack_tape L.c4
  obtain ⟨e1, e2, _, _, _, _, e7⟩ := endP_spec
    { target := T, first := G2.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } ms yy
  rw [← hq] at e1 e2 e7
  have hy : yy.1 = Weight.atZero 3 := by rw [hyy]
  have hv' : q.vars.toList = (ms ++ [yy]).map (·.1) := e1
  have hr : q.r.toList = (ms ++ [yy]).map (·.2.2) := e2
  have hfirst : q.first = G2.next := e7
  have hwl : q.walk.1.length = ownOf 0 hp.lamS 2 := by
    rw [walk_length (by simp) hv' hr hheld, List.map_append, a1, List.map_singleton, hy]
    refine (entries_count _ (fun w hw => ?_) 2).trans ?_
    · rw [(List.mem_replicate.1 hw).2]
      rfl
    · rw [plainWs, List.length_replicate]
  have hS2' : Sized ({ G2 with next := G2.next + 1 + 2 * hp.lamS + 2 + (2 + (1 + P.y.LamM) +
      (hp.NCL - (if (g == 0) = true then 1 else 0))) } : Fork) := L.s2
  obtain ⟨_, sGs, _, _⟩ := hideRun_ok _ Gs _ _ _ hS2' hGs
  rw [hfirst, hwl] at hG3
  -- the merge
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := hear_ended (hear_of_flat c7)
  obtain ⟨q1, k1⟩ := level_own L.s4 c1 G L.g7
  obtain ⟨q5, k5⟩ := level_own L.s3 c5 G L.g3'
  obtain ⟨q6, k6⟩ := level_own L.s3' L.c6 G L.g4
  refine
    { sized := (flatForkEnd_slots L.sG5 c7).2.2.1
      sq := fun j hj => ?_
      terms := fun tT' hT' => ?_
      stack := fun j hj => ?_
      lv1 := fun j hj => ?_
      lv2 := fun o2 h2 j hj => ?_
      pV := by rw [a5, a4]; rfl
      wV := by rw [L.kTV]; exact tsc_len c2
      pM := fun o2 h2 => ?_
      wM := ?_ }
  · rw [L.kWpl] at hj
    obtain rfl : j = F4.next := by omega
    exact k1
  · have e : o.H.tT = some { t0 with p := p' } := by rw [hH]
    obtain rfl : ({ t0 with p := p' } : Tsc) = tT' := Option.some.inj (e.symm.trans hT')
    show OwnUnder G (t0.sCl + 1) _
    rw [hsCl, ← tP]
    exact run_under sK1 hR L.g2
  · obtain rfl : j = G2.next := by
      rw [hsA0] at hj
      unfold ownOf at hj
      omega
    exact run_under sGs hG3 L.g3
  · obtain rfl : j = G3.next := by omega
    exact k5
  · obtain rfl : hd2 = o2 := Option.some.inj (L.eHd2.symm.trans h2)
    obtain rfl : j = G3'.next := by omega
    exact k6
  · obtain rfl : hd2' = o2 := Option.some.inj (h2'.symm.trans h2)
    have enx : (k4Slots P hp g F.next).nx = (k4Slots P hp g F.next).h2L + 2 := rfl
    by_cases hg : (g == 0) = true
    · have e := (hear_end_first Reading.gl hF h' hg).2.1
      rw [if_pos hg]
      omega
    · have e := (hear_end_later Reading.gl hF h' (Bool.eq_false_iff.2 hg)).2.1
      rw [if_neg hg]
      omega
  · rw [hE.walkLen]
    refine (entries_count _ (fun w hw => ?_) 1).trans ?_
    · rw [(List.mem_replicate.1 hw).2]
      rfl
    · rw [List.length_replicate]

/-- **What the run "front" lays under the own slots of the token sumcheck on the row products.** F₀:
the ledger from which it runs. F₁: the ledger that it leaves. -/
theorem front_own {rows : Bool} {P' : OnBytes.Model.Layer.Pub} {g' : Nat} {o : Own}
    {F₀ F₁ : Fork} {fs : Array Aff} {n : Nat} (hS : Sized F₀) (hw : o.H.tV.p.walk.1.length = n)
    (h : formsFrontWith rows P' g' o F₀ = some (fs, F₁)) : OwnUnder F₁ o.H.tV.p.first n := by
  obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, e⟩ := formsFrontWith_some h
  rw [hw] at r1
  refine (run_under hS r1 (Fo.Later.refl F1)).later ?_
  rw [e]
  refine (OnBytes.PscRun.hideRun_keeps r2).trans ?_
  split
  · exact (OnBytes.PscRun.paid_later F2 _).trans (OnBytes.PscRun.paid_later _ _)
  · exact OnBytes.PscRun.paid_later F2 _

/-- **What the run "back" lays under the merge's own slots.** F₁: the ledger from which it runs. F₂:
the ledger that it leaves. -/
theorem back_own {o : Own} {F₁ F₂ : Fork} {fs : Array Aff} {n : Nat} (hS : Sized F₁)
    (hw : o.wo.p.walk.1.length = n) (h : formsBack o F₁ = some (fs, F₂)) :
    OwnUnder F₂ o.wo.p.first n := by
  obtain ⟨F1, _, r1, e⟩ := formsBack_some h
  rw [hw] at r1
  refine (run_under hS r1 (Fo.Later.refl F1)).later ?_
  rw [e]
  exact OnBytes.PscRun.paid_later F1 _

/-- The run "front" finds these slots not filled in the ledger from which it runs. -/
theorem front_free {rows : Bool} {P' : OnBytes.Model.Layer.Pub} {g' : Nat} {o : Own}
    {F₀ F₁ : Fork} {fs : Array Aff} {n : Nat} (hS : Sized F₀) (hw : o.H.tV.p.walk.1.length = n)
    (h : formsFrontWith rows P' g' o F₀ = some (fs, F₁)) :
    ∀ e, e < n → ¬ Filled F₀ (o.H.tV.p.first + e) := by
  intro e he
  obtain ⟨_, _, _, F1, _, _, _, _, _, r1, _, _⟩ := formsFrontWith_some h
  rw [hw] at r1
  exact ((hideRun_ok F₀ F1 _ _ _ hS r1).2.2.1 e (by rw [Array.size_replicate]; exact he)).2.1

/-- The run "back" finds these slots not filled in the ledger from which it runs. -/
theorem back_free {o : Own} {F₁ F₂ : Fork} {fs : Array Aff} {n : Nat} (hS : Sized F₁)
    (hw : o.wo.p.walk.1.length = n) (h : formsBack o F₁ = some (fs, F₂)) :
    ∀ e, e < n → ¬ Filled F₁ (o.wo.p.first + e) := by
  intro e he
  obtain ⟨F1, _, r1, _⟩ := formsBack_some h
  rw [hw] at r1
  exact ((hideRun_ok F₁ F1 _ _ _ hS r1).2.2.1 e (by rw [Array.size_replicate]; exact he)).2.1

/-! ## 3 Public numbers -/

/-- How many slots of its own a sumcheck of each of the three shapes has. -/
theorem own_shapes (mu lt lam dY n : Nat) :
    ownSlots (k4LevelShape mu).all = ownOf 0 mu 2 ∧
      ownSlots (k4TokenShape lt dY n).all = ownOf 0 lt dY ∧
      ownSlots (k4PlainShape lam dY n).all = ownOf 0 lam dY := by
  obtain ⟨a, b, c⟩ := ownRun_shapes mu lt lam dY n
  have a' : 0 + ownSlots (k4LevelShape mu).all = ownOf 0 mu 2 := a
  have b' : 1 + ownSlots (k4TokenShape lt dY n).all = ownOf 1 lt dY := b
  have c' : 0 + ownSlots (k4PlainShape lam dY n).all = ownOf 0 lam dY := c
  unfold ownOf at a' b' c' ⊢
  omega

/-- **The coins in front of the merge's part, and in the whole row**: behind the merge's first run
of coins the row has one coin more. -/
theorem row_own_nums (Q : K4Pub) :
    spentTo (k4RowIn Q) (k0 Q.g + 15) =
        spentTo (k4RowIn Q) (k0 Q.g + 14) + (if Q.g == 0 then 1 else 0) ∧
      spentTo (k4RowIn Q) (k4RowIn Q).length =
        spentTo (k4RowIn Q) (k0 Q.g + 15) + ownOf 0 Q.P.wsLay.lk 1 + 1 := by
  have C : ∀ j, spentTo (k4RowIn Q) (k0 Q.g + j) = (((k4Tail Q).map coinsIn).take j).sum := by
    intro j
    rw [k4RowIn_all, spentTo_quiet]
    show (((k4Tail Q).take j).map coinsIn).sum = _
    rw [List.map_take]
  have len : (k4RowIn Q).length = k0 Q.g + 16 := by
    rw [k4RowIn_all, List.length_append, List.length_replicate]
    rfl
  have c14 := C 14
  have c15 := C 15
  have c16 := C 16
  rw [k4Tail_coins] at c14 c15 c16
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at c14 c15 c16
  refine ⟨?_, ?_⟩
  · rw [c15, c14]
    omega
  · rw [len, c16, c15]
    omega

/-- **Each sumcheck's first run of coins ends in front of the row's last coin.** -/
theorem row_bounds (Q : K4Pub) :
    spentTo (k4RowIn Q) (k0 Q.g + 2) + ownOf 0 Q.P.rd.muV 2 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 5) + ownOf 1 Q.P.y.h.lt 2 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 6) + ownOf 1 Q.P.y.h.lt 1 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 8) + ownOf 0 Q.hp.lamS 2 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 9) + ownOf 0 Q.P.rd.muH 2 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 12) + ownOf 0 Q.P.rd.muH2 2 <
        spentTo (k4RowIn Q) (k4RowIn Q).length ∧
      spentTo (k4RowIn Q) (k0 Q.g + 15) + ownOf 0 Q.P.wsLay.lk 1 <
        spentTo (k4RowIn Q) (k4RowIn Q).length := by
  have R := k4_row_nums Q
  obtain ⟨r15, rAll⟩ := row_own_nums Q
  have cP := R.cP
  have c2 := R.c2
  have c3 := R.c3
  have c4 := R.c4
  have c5 := R.c5
  have c6 := R.c6
  have cE := R.cE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **SLOT = n + COIN, at the seven runs of own slots**: where each run of own slots lies, by the
number of coins that the row spends in front of the sumcheck's part. A level's and the batched
sumcheck's by the slot behind the run; a token sumcheck's by the slot in front of it; the merge's
by its first own slot. -/
structure OwnStarts (Q : K4Pub) (o : Own) (n : Nat) : Prop where
  sq : o.H.wpl.sL = n + (spentTo (k4RowIn Q) (k0 Q.g + 2) + ownOf 0 Q.P.rd.muV 2)
  rows : o.H.tV.sCl = n + spentTo (k4RowIn Q) (k0 Q.g + 5)
  terms : ∀ tT, o.H.tT = some tT → tT.sCl = n + spentTo (k4RowIn Q) (k0 Q.g + 6)
  stack : o.K.sA0 = n + (spentTo (k4RowIn Q) (k0 Q.g + 8) + ownOf 0 Q.hp.lamS 2)
  lv1 : o.hd.sL = n + (spentTo (k4RowIn Q) (k0 Q.g + 9) + ownOf 0 Q.P.rd.muH 2)
  lv2 : ∀ o2, o.hd2 = some o2 →
    o2.sL = n + (spentTo (k4RowIn Q) (k0 Q.g + 12) + ownOf 0 Q.P.rd.muH2 2)
  merge : o.wo.p.first = n + spentTo (k4RowIn Q) (k0 Q.g + 15)

/-- The hearing's numbers and the row's give it. -/
theorem own_starts {Q : K4Pub} {o : Own} {n : Nat} (N : K4Nums Q.P Q.hp Q.g o n)
    (pM : ∀ o2, o.hd2 = some o2 →
      o.wo.p.first = o2.sL + 2 + (if (Q.g == 0) = true then 1 else 0)) : OwnStarts Q o n := by
  have R := k4_row_nums Q
  obtain ⟨r15, _⟩ := row_own_nums Q
  obtain ⟨tT, hT⟩ := N.hasT
  obtain ⟨o2, h2⟩ := N.has2
  obtain ⟨t1, t2, t3⟩ := N.terms tT hT
  obtain ⟨g1, _, _⟩ := N.lv2 o2 h2
  have m1 := pM o2 h2
  have nL := N.sL
  have nPv := N.sPv
  have nCl := N.sCl
  have nEnd := N.sEnd
  have nhL := N.hL
  have c1 := R.c1
  have cP := R.cP
  have c2 := R.c2
  have c3 := R.c3
  have c4 := R.c4
  have c5 := R.c5
  have c6 := R.c6
  have cE := R.cE
  refine
    { sq := by omega
      rows := by omega
      terms := fun tT' hT' => ?_
      stack := by omega
      lv1 := by omega
      lv2 := fun o2' h2' => ?_
      merge := by omega }
  · obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans hT')
    omega
  · obtain rfl : o2 = o2' := Option.some.inj (h2.symm.trans h2')
    omega

/-- **The seven parts in the row**: five at the jobs of which Law/FlatTops.lean speaks; the second
token sumcheck's and the batched sumcheck's at a job of the row's shape. -/
theorem row_jobs (Q : K4Pub) :
    (∃ a b, (k4RowIn Q)[k0 Q.g + 2]? = some (sumPart a b (squaresSum Q))) ∧
    (∃ a b, (k4RowIn Q)[k0 Q.g + 5]? = some (sumPart a b (rowsSum Q))) ∧
    (∃ a b J, (k4RowIn Q)[k0 Q.g + 6]? = some (sumPart a b J) ∧
      J.shape = k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) ∧
    (∃ a b J, (k4RowIn Q)[k0 Q.g + 8]? = some (sumPart a b J) ∧
      J.shape = k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g)) ∧
    (∃ a b, (k4RowIn Q)[k0 Q.g + 9]? = some (sumPart a b (gatedSum Q))) ∧
    (∃ a b, (k4RowIn Q)[k0 Q.g + 12]? = some (sumPart a b (gated2Sum Q))) ∧
    ∃ a b, (k4RowIn Q)[k0 Q.g + 15]? = some (sumPart a b (mergeSum Q)) :=
  ⟨⟨_, _, k4RowIn_at Q 2⟩, ⟨_, _, k4RowIn_at Q 5⟩, ⟨_, _, _, k4RowIn_at Q 6, rfl⟩,
    ⟨_, _, _, k4RowIn_at Q 8, rfl⟩, ⟨_, _, k4RowIn_at Q 9⟩, ⟨_, _, k4RowIn_at Q 12⟩,
    ⟨_, _, k4RowIn_at Q 15⟩⟩

/-! ## 4 A part of the lent row, its coins, and the world -/

section
variable {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub}

/-- **Part number i of the row, as the book lends it coins, is the masked sumcheck's part at the job
J, seated as the row seats it; it is handed cp.** It is a definition: a premise's form. Nothing is
claimed of it. -/
def SumAt (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) (i : Nat)
    (name endName : String) (J : SumJob K4In Unit) (cp : SumCoins name endName J) : Prop :=
  rowAt? (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts c i =
    some ⟨k4SeatOf Q cells weights tokens (look Q) (sumPart name endName J), cp⟩

/-- Where the row at the small input has that part, the lent row hands it something. -/
theorem sumAt_some (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (i : Nat) (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) : ∃ cp, SumAt c i name endName J cp := by
  have hpart : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts[i]? =
      some (k4SeatOf Q cells weights tokens (look Q) (sumPart name endName J)) := by
    show ((k4RowIn Q).map _)[i]? = _
    rw [List.getElem?_map, hp]
    rfl
  exact rowAt_some _ c _ _ hpart

/-- **Below the number of own slots `hidingCoin` reads a member of the part's first run of coins**:
the place that it reads lies inside that list. General in the job. -/
theorem hidingCoin_there {W Z : Type} {name endName : String} {J : SumJob W Z}
    (cp : SumCoins name endName J) (e : Nat) (he : e < ownSlots J.shape.all) :
    J.shape.lead + e < (firstRun cp).length := by
  have hl : (firstRun cp).length = ownRun J.shape := by simp [firstRun, coinsE]
  rw [hl]
  unfold ownRun
  omega

/-- **The coin for coefficient number e is the row's coin number `spentTo` + the call's lead + e**,
at a part of the lent row. (Law/FlatCoins.lean has the like at a row whose parts are not seated.) -/
theorem hidingCoin_seated
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts} {i : Nat}
    {name endName : String} {J : SumJob K4In Unit} {cp : SumCoins name endName J}
    (hcp : SumAt c i name endName J cp) (e : Nat) (he : e < ownSlots J.shape.all) :
    hidingCoin cp e = Reading.gl.val
      ((spentOf _ c).getD (spentTo (k4RowIn Q) i + (J.shape.lead + e)) zeroE) := by
  have hown : J.shape.lead + e < ownRun J.shape := by
    unfold ownRun
    omega
  have hcoin := (k4_coin i (sumPart (V := Unit) name endName J) cp hcp (J.shape.lead + e)
      (Nat.lt_of_lt_of_le hown (Nat.le_add_right _ _))).trans
    (runsE_first (name, ⟨0, ownRun J.shape⟩) (endRuns endName J.shape.ends) cp.2.1
      (J.shape.lead + e) hown)
  rw [hcoin]
  rfl

/-- **ONE STATEMENT, GENERAL IN THE PART.** G: a ledger under whose slots from j0 on lie 0 and the
factor -1. n: the slot under which the row's first coin lies. The mask row holds the row's coins
from n on, but for the last. So in the world of every later ledger own slot number e is worth the
part's coin for coefficient number e, at every input w and front fr of the call. -/
theorem own_field {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}
    {G F : Fork} {mask : Nat → Cb.Gl.E} {n i : Nat} {name endName : String}
    {J : SumJob K4In Unit} {cp : SumCoins name endName J} (hL : Later G F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hmask : ∀ j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
      mask (n + j) = Reading.gl.val ((spentOf _ c).getD j zeroE))
    (hcp : SumAt c i name endName J cp) (j0 : Nat) (hU : OwnUnder G j0 (ownSlots J.shape.all))
    (hn : j0 = n + (spentTo (k4RowIn Q) i + J.shape.lead))
    (hb : spentTo (k4RowIn Q) i + ownRun J.shape < spentTo (k4RowIn Q) (k4RowIn Q).length)
    (w : K4In) (fr : Front Unit) :
    ∀ e, e < ownSlots (J.callAt w fr).all →
      (F.worldOf Reading.gl mask entry).slot (j0 + e) = hidingCoin cp e := by
  intro e he
  rw [ownSlots_callAt] at he
  refine slot_value entry (hU e he) hL (coin := hidingCoin cp e) ?_ ?_
  · rw [Reading.gl.zero, Reading.gl.sub, Reading.gl.zero, Reading.gl.one]
    ring
  · rw [hn, Nat.add_assoc, Nat.add_assoc, hidingCoin_seated hcp e he]
    refine hmask _ ?_
    unfold ownRun at hb
    omega

end

/-- The world of the ledger F on the mask row that is read off the witness behind the member's step,
at the continuation ds' of the challenges heard: the world of `opened_left` (Law/SlotsTrue.lean). -/
abbrev worldBehind (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) (k : Coins Bk)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) X) (A : VerifiableInference.Desc.K9.Part)
    (ds' : List Fmt.Drawn) (F : Fork) (entry : Nat → Nat → Nat → Cb.Gl.E) : World Cb.Gl.E :=
  F.worldOf Reading.gl
    (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask entry

variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **What each of the seven begins with.** a: the open segment's part in front of the member: the
slots are counted from its ledger's next slot. The last clause: at whatever the book lends the row.
-/
theorem own_ground
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ∃ a : VerifiableInference.Desc.K9.Part, segAt? s = some a ∧
      HeardOwn Q.P Q.hp Q.g o A.F ∧ K4Nums Q.P Q.hp Q.g o a.F.next ∧
      ∀ c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts,
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
          (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
        ∀ ds' j, j + 1 < spentTo (k4RowIn Q) (k4RowIn Q).length →
          (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask (a.F.next + j) =
            Reading.gl.val ((spentOf _ c).getD j zeroE) := by
  obtain ⟨a, c', ha, _, N, Pl, hmask⟩ := stand_ground Z
  obtain ⟨a', a₀, fo, ha', ha0, haF, _, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  have hSd : Sized a.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  have H := hear_own hSd hh
  refine ⟨a, ha, ⟨H.sized, H.sq, H.terms, H.stack, H.lv1, H.lv2, H.pV, H.wV, H.pM, H.wM⟩, N,
    fun c hc => ?_⟩
  obtain rfl : c' = c := Except.ok.inj (Pl.lent.symm.trans hc)
  exact hmask

/-! ## 5 The seven -/

/-- **THE SQUARES' LEVEL.** Fj: the ledger from which the verifier's flat function of that level has
run; its point, claimed form, order and tape are free. F: any ledger later than the one that the
step leaves. CONDITIONAL on the named premises. -/
theorem squares_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (cp : SumCoins name endName (squaresSum Q))
    (hcp : SumAt c (k0 Q.g + 2) name endName (squaresSum Q) cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    {rho : Array OnBytes.E} {C : Aff} {order : List Nat} {Fj G2 : Fork} {tp u : Tape}
    (hF : Fl.levelIn Q.P.rd.muV rho C order Fj tp = some (o.H.wpl, G2, u))
    (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots ((squaresSum Q).callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (Fj.next + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsL, _⟩ := levelIn_heard hF
  have hj : Fj.next + ownOf 0 Q.P.rd.muV 2 = o.H.wpl.sL := by
    rw [hsL]
    unfold ownOf
    omega
  have hU : OwnUnder A.F Fj.next (ownSlots (squaresSum Q).shape.all) := by
    rw [show ownSlots (squaresSum Q).shape.all = ownOf 0 Q.P.rd.muV 2 from
      (own_shapes Q.P.rd.muV 0 0 0 0).1]
    exact H.sq _ hj
  refine own_field hL entry (hm c hc ds') hcp Fj.next hU ?_ ?_ st.input (frontOf st seen)
  · show Fj.next = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 2) + 0)
    have e := S.sq
    omega
  · rw [show ownRun (squaresSum Q).shape = ownOf 0 Q.P.rd.muV 2 from
      (ownRun_shapes Q.P.rd.muV 0 0 0 0).1]
    exact (row_bounds Q).1

/-- **THE TOKEN SUMCHECK ON THE ROW PRODUCTS: LAID LATE, BY "front".** F₁: the ledger that "front"
leaves, run from the ledger that the step leaves. F: any ledger later than F₁. F0: the ledger from
which the verifier's flat function of that sumcheck has run, in front of the claimed sum's laying;
its point, numbers and tape are free. CONDITIONAL on the named premises. -/
theorem rows_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (cp : SumCoins name endName (rowsSum Q))
    (hcp : SumAt c (k0 Q.g + 5) name endName (rowsSum Q) cp)
    (ds' : List Fmt.Drawn) {rows : Bool} {P' : OnBytes.Model.Layer.Pub} {g' : Nat}
    {fs₁ : Array Aff} {F₁ : Fork}
    (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁)) (F : Fork) (hL : Later F₁ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    {PV : Array OnBytes.E} {lt nE dY : Nat} {F0 G2 : Fork} {tp u : Tape}
    (hF : Fl.tscIn PV lt nE dY F0 tp = some (o.H.tV, G2, u))
    (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (F0.next + 1 + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  have hsCl : o.H.tV.sCl = F0.next := (tscIn_heard hF).2.2.2.2.2.2.2.2.2.2.1
  have hU : OwnUnder F₁ (F0.next + 1) (ownSlots (rowsSum Q).shape.all) := by
    rw [show ownSlots (rowsSum Q).shape.all = ownOf 0 Q.P.y.h.lt 2 from
      (own_shapes 0 Q.P.y.h.lt 0 2 _).2.1, ← hsCl, ← H.pV]
    exact front_own H.sized H.wV hf
  refine own_field hL entry (hm c hc ds') hcp (F0.next + 1) hU ?_ ?_ st.input (frontOf st seen)
  · show F0.next + 1 = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 5) + 1)
    have e := S.rows
    omega
  · rw [show ownRun (rowsSum Q).shape = ownOf 1 Q.P.y.h.lt 2 from
      (ownRun_shapes 0 Q.P.y.h.lt 0 2 _).2.1]
    exact (row_bounds Q).2.1

/-- **THE SECOND TOKEN SUMCHECK.** J: the job of the row's part, of the row's shape (`row_jobs`). F:
any ledger later than the one that the step leaves. CONDITIONAL on the named premises. -/
theorem terms_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (J : SumJob K4In Unit) (hsh : J.shape = k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))
    (cp : SumCoins name endName J) (hcp : SumAt c (k0 Q.g + 6) name endName J cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (tT : Tsc) (hT : o.H.tT = some tT) (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots (J.callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (tT.sCl + 1 + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  have hU : OwnUnder A.F (tT.sCl + 1) (ownSlots J.shape.all) := by
    rw [hsh, (own_shapes 0 Q.P.y.h.lt 0 1 _).2.1]
    exact H.terms tT hT
  refine own_field hL entry (hm c hc ds') hcp (tT.sCl + 1) hU ?_ ?_ st.input (frontOf st seen)
  · rw [hsh]
    show tT.sCl + 1 = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 6) + 1)
    have e := S.terms tT hT
    omega
  · rw [hsh, (ownRun_shapes 0 Q.P.y.h.lt 0 1 _).2.1]
    exact (row_bounds Q).2.2.1

/-- **THE BATCHED SUMCHECK.** J: the job of the row's part, of the row's shape (`row_jobs`). j0: its
first own slot: as many slots as it has of its own reach from j0 to its first end value's slot. F:
any ledger later than the one that the step leaves. CONDITIONAL on the named premises. -/
theorem stack_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (J : SumJob K4In Unit) (hsh : J.shape = k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g))
    (cp : SumCoins name endName J) (hcp : SumAt c (k0 Q.g + 8) name endName J cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (j0 : Nat) (hj : j0 + ownOf 0 Q.hp.lamS 2 = o.K.sA0) (st : State K4In Unit)
    (seen : Seen) :
    ∀ i, i < ownSlots (J.callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (j0 + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  have hU : OwnUnder A.F j0 (ownSlots J.shape.all) := by
    rw [hsh, (own_shapes 0 0 Q.hp.lamS 2 _).2.2]
    exact H.stack j0 hj
  refine own_field hL entry (hm c hc ds') hcp j0 hU ?_ ?_ st.input (frontOf st seen)
  · rw [hsh]
    show j0 = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 8) + 0)
    have e := S.stack
    omega
  · rw [hsh, (ownRun_shapes 0 0 Q.hp.lamS 2 _).2.2]
    exact (row_bounds Q).2.2.2.1

/-- **THE FIRST GATED LEVEL.** Fj: the ledger from which the verifier's flat function of that
level has run; its point, claimed form, order and tape are free. F: any ledger later than the one
that the step leaves. CONDITIONAL on the named premises. -/
theorem gated_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (cp : SumCoins name endName (gatedSum Q))
    (hcp : SumAt c (k0 Q.g + 9) name endName (gatedSum Q) cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    {rho : Array OnBytes.E} {C : Aff} {order : List Nat} {Fj G2 : Fork} {tp u : Tape}
    (hF : Fl.levelIn Q.P.rd.muH rho C order Fj tp = some (o.hd, G2, u))
    (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots ((gatedSum Q).callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (Fj.next + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsL, _⟩ := levelIn_heard hF
  have hj : Fj.next + ownOf 0 Q.P.rd.muH 2 = o.hd.sL := by
    rw [hsL]
    unfold ownOf
    omega
  have hU : OwnUnder A.F Fj.next (ownSlots (gatedSum Q).shape.all) := by
    rw [show ownSlots (gatedSum Q).shape.all = ownOf 0 Q.P.rd.muH 2 from
      (own_shapes Q.P.rd.muH 0 0 0 0).1]
    exact H.lv1 _ hj
  refine own_field hL entry (hm c hc ds') hcp Fj.next hU ?_ ?_ st.input (frontOf st seen)
  · show Fj.next = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 9) + 0)
    have e := S.lv1
    omega
  · rw [show ownRun (gatedSum Q).shape = ownOf 0 Q.P.rd.muH 2 from
      (ownRun_shapes Q.P.rd.muH 0 0 0 0).1]
    exact (row_bounds Q).2.2.2.2.1

/-- **THE SECOND GATED LEVEL.** Fj: the ledger from which the verifier's flat function of that
level has run; its point, claimed form, order and tape are free. F: any ledger later than the one
that the step leaves. CONDITIONAL on the named premises. -/
theorem gated2_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (cp : SumCoins name endName (gated2Sum Q))
    (hcp : SumAt c (k0 Q.g + 12) name endName (gated2Sum Q) cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (o2 : Level) (h2 : o.hd2 = some o2)
    {rho : Array OnBytes.E} {C : Aff} {order : List Nat} {Fj G2 : Fork} {tp u : Tape}
    (hF : Fl.levelIn Q.P.rd.muH2 rho C order Fj tp = some (o2, G2, u))
    (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots ((gated2Sum Q).callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (Fj.next + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsL, _⟩ := levelIn_heard hF
  have hj : Fj.next + ownOf 0 Q.P.rd.muH2 2 = o2.sL := by
    rw [hsL]
    unfold ownOf
    omega
  have hU : OwnUnder A.F Fj.next (ownSlots (gated2Sum Q).shape.all) := by
    rw [show ownSlots (gated2Sum Q).shape.all = ownOf 0 Q.P.rd.muH2 2 from
      (own_shapes Q.P.rd.muH2 0 0 0 0).1]
    exact H.lv2 o2 h2 _ hj
  refine own_field hL entry (hm c hc ds') hcp Fj.next hU ?_ ?_ st.input (frontOf st seen)
  · show Fj.next = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 12) + 0)
    have e := S.lv2 o2 h2
    omega
  · rw [show ownRun (gated2Sum Q).shape = ownOf 0 Q.P.rd.muH2 2 from
      (ownRun_shapes Q.P.rd.muH2 0 0 0 0).1]
    exact (row_bounds Q).2.2.2.2.2.1

/-- **THE MERGE: LAID LATE, BY "back".** F₁: a ledger later than the one that the step leaves. F₂:
the ledger that "back" leaves, run from F₁. F: any ledger later than F₂. Fj: the ledger from which
the verifier's flat function of the merge has run: its arrays have their sizes; the layout, the
claims, their slots and the tape are free. CONDITIONAL on the named premises. -/
theorem merge_hs
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (cp : SumCoins name endName (mergeSum Q))
    (hcp : SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp)
    (ds' : List Fmt.Drawn) {F₁ F₂ : Fork} {fs₂ : Array Aff} (h1 : Later A.F F₁)
    (hb : formsBack o F₁ = some (fs₂, F₂)) (F : Fork) (hL : Later F₂ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    {lay : OnBytes.Model.WsLay} {cl : Array WsClaim} {sv : Array Nat} {Fj G2 : Fork} {tp u : Tape}
    (hS : Sized Fj) (hF : flatForkEnd lay cl sv Fj tp = some (o.wo, G2, u))
    (st : State K4In Unit) (seen : Seen) :
    ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (Fj.next + i) = hidingCoin cp i := by
  obtain ⟨a, _, H, N, hm⟩ := own_ground Z
  have S := own_starts N H.pM
  have hfirst : o.wo.p.first = Fj.next := (flatForkEnd_slots hS hF).1
  have hU : OwnUnder F₂ Fj.next (ownSlots (mergeSum Q).shape.all) := by
    rw [show ownSlots (mergeSum Q).shape.all = ownOf 0 Q.P.wsLay.lk 1 from
      (own_shapes 0 0 Q.P.wsLay.lk 1 1).2.2, ← hfirst]
    exact back_own (h1.sized H.sized) H.wM hb
  refine own_field hL entry (hm c hc ds') hcp Fj.next hU ?_ ?_ st.input (frontOf st seen)
  · show Fj.next = a.F.next + (spentTo (k4RowIn Q) (k0 Q.g + 15) + 0)
    have e := S.merge
    omega
  · rw [show ownRun (mergeSum Q).shape = ownOf 0 Q.P.wsLay.lk 1 from
      (ownRun_shapes 0 0 Q.P.wsLay.lk 1 1).2.2]
    exact (row_bounds Q).2.2.2.2.2.2

/-! ## 6 Two of the seven in another form -/

/-- The second token sumcheck, in the form in which the general statements on the masked sumcheck's
part ask it (Law/SumEndJobs.lean): at the first own slot that the part's text of the verifier hands
back. Fh: the ledger from which that text runs. -/
example
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (J : SumJob K4In Unit) (hsh : J.shape = k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))
    (cp : SumCoins name endName J) (hcp : SumAt c (k0 Q.g + 6) name endName J cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (tT : Tsc) (hT : o.H.tT = some tT) (st : State K4In Unit) (seen : Seen)
    (C : Aff) (Fh G : Fork) (rounds : List Fmt.RoundView)
    (h : VerifiableInference.Desc.Part.MaskedSum.Heard)
    (hh : VerifiableInference.Desc.Part.MaskedSum.hear C (J.callAt st.input (frontOf st seen)) Fh
      rounds = some (h, G))
    (hn : Fh.next = tT.sCl + 1) :
    ∀ i, i < ownSlots (J.callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (h.first + i) = hidingCoin cp i := by
  rw [heard_first hh, hn]
  exact terms_hs Z c hc name endName J hsh cp hcp ds' F hL entry tT hT st seen

/-- The batched sumcheck, in the same form. -/
example
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts)
    (hc : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c)
    (name endName : String)
    (J : SumJob K4In Unit) (hsh : J.shape = k4PlainShape Q.hp.lamS 2 (nStack Q.P Q.hp Q.g))
    (cp : SumCoins name endName J) (hcp : SumAt c (k0 Q.g + 8) name endName J cp)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (st : State K4In Unit) (seen : Seen) (C : Aff) (Fh G : Fork) (rounds : List Fmt.RoundView)
    (h : VerifiableInference.Desc.Part.MaskedSum.Heard)
    (hh : VerifiableInference.Desc.Part.MaskedSum.hear C (J.callAt st.input (frontOf st seen)) Fh
      rounds = some (h, G))
    (hn : Fh.next + ownOf 0 Q.hp.lamS 2 = o.K.sA0) :
    ∀ i, i < ownSlots (J.callAt st.input (frontOf st seen)).all →
      (worldBehind T own rdOf k y A ds' F entry).slot (h.first + i) = hidingCoin cp i := by
  rw [heard_first hh]
  exact stack_hs Z c hc name endName J hsh cp hcp ds' F hL entry Fh.next hn st seen

end ProofFile.Honest.K4.SlotsOwn

#print axioms ProofFile.Honest.K4.SlotsOwn.OwnUnder.later
#print axioms ProofFile.Honest.K4.SlotsOwn.run_under
#print axioms ProofFile.Honest.K4.SlotsOwn.entries_count
#print axioms ProofFile.Honest.K4.SlotsOwn.level_own
#print axioms ProofFile.Honest.K4.SlotsOwn.tsc_len
#print axioms ProofFile.Honest.K4.SlotsOwn.hear_own
#print axioms ProofFile.Honest.K4.SlotsOwn.front_own
#print axioms ProofFile.Honest.K4.SlotsOwn.back_own
#print axioms ProofFile.Honest.K4.SlotsOwn.front_free
#print axioms ProofFile.Honest.K4.SlotsOwn.back_free
#print axioms ProofFile.Honest.K4.SlotsOwn.own_shapes
#print axioms ProofFile.Honest.K4.SlotsOwn.row_own_nums
#print axioms ProofFile.Honest.K4.SlotsOwn.row_bounds
#print axioms ProofFile.Honest.K4.SlotsOwn.own_starts
#print axioms ProofFile.Honest.K4.SlotsOwn.row_jobs
#print axioms ProofFile.Honest.K4.SlotsOwn.sumAt_some
#print axioms ProofFile.Honest.K4.SlotsOwn.hidingCoin_there
#print axioms ProofFile.Honest.K4.SlotsOwn.hidingCoin_seated
#print axioms ProofFile.Honest.K4.SlotsOwn.own_field
#print axioms ProofFile.Honest.K4.SlotsOwn.own_ground
#print axioms ProofFile.Honest.K4.SlotsOwn.squares_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.rows_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.terms_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.stack_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.gated_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.gated2_hs
#print axioms ProofFile.Honest.K4.SlotsOwn.merge_hs
