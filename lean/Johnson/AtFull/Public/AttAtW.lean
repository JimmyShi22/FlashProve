-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AttAtW.lean: THE ATTENTION's SIDE OF publicOfO (step P14) AT THE WRITTEN
  VALUES: config_returns.
RE-CUT BY PROGRAM out of an earlier working file of this project, which is not in this repository
  (sha256 9ec468ab…), its lines 818-1014, LESS ITS OWN COPY OF THE TACTIC kernel_rfl (ten lines),
which no line of this file or folder uses (the tactic's one place is
  Johnson/Unfolds/KernelRfl.lean): NO OTHER LETTER OF LEAN TURNS.
What is not claimed: the exponentials' digest's equation (hT). The recursion limit is raised in this
  file (maxRecDepth 1000000).

Nothing on soundness.
-/
import Johnson.AtFull.Public.AttLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial.AttAtW
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road.K4.Trial.AttLaws
open OnBytes.Road.L5 (refL)
open OnBytes.Tie.Pv.Plan (scalesF)
open VerifierAndGoals.Lines (callsRef)
open VerifiableInference.PlanWritten (tableHeldO)
open VerifiableInference.PlanWritten.Attention (configO configS callsDigestO)

/-- The strict scan's WRITTEN value at the stored free numbers. -/
def PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- The layers' shape at that value. -/
def hW : Layer.Shape := Verify.layerShape PW

/-- The number that names group g's matrix qa: publicOfO's own term (PublicAt.lean:150). -/
def mqOf (y : Lay) (g : Nat) : Nat := (((Layer.tailsOf y).getD g {}).mats.getD (Layer.matIx y).iQA
    {}).aId

/-- A layout with the three fields that layoutLook sets (LayerLayout.lean:615). -/
def lookAt (y0 : Lay) (cl : Array Call) (fo : Forest.Shape) (kbm : Nat) : Lay :=
  { y0 with cl := cl, fo := fo, kbm := kbm }

/-- layoutLook's own first line (LayerLayout.lean:604). -/
def clOf (y : Lay) : Array Call := y.calls.mapIdx fun q cd => y.callRecord q cd

/-- layoutLook's padding counts (LayerLayout.lean:610-611), or none where its loop refuses: A CLOSED
  TERM THAT NO FACT HERE OPENS. -/
def pubOf (y : Lay) (fo : Forest.Shape) : Array Nat :=
  ((y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub) (Forest.noPub
      fo)).toOption.getD #[]

/-- A layout of the form that layoutLook returns (LayerLayout.lean:615). -/
def lookC (y0 : Lay) (fo : Forest.Shape) (kbm : Nat) : Lay :=
  lookAt y0 (clOf y0) { fo with pub := pubOf y0 fo } kbm

/-- A test at that layout, made of the first half's value, the forest's numbers (without the tests
  on the calls' tables: the twin
shapeNoAsk) and the columns of matrix b. NO FREE LETTER: with one in the layout the kernel says
  "deep recursion detected" at the attention's
group. -/
def withLookC (f : Lay → Bool) : Bool :=
  onOk (baseNoFill hW callsRef) fun y0 => onOk (Forest.shapeNoAsk (clOf y0) y0.h.lidb) fun fo =>
    onOk (Forest.planeCols fo y0.h.lmb) fun kbm => f (lookC y0 fo kbm)

/-- What the attention's arm reads of a plan (armOf, Johnson/Desc/First/Link/RowsRun.lean:88-90),
  WRITTEN: off a print of
Lean's evaluator at the verifier's own Attention.group (by a sheet that is not in this repository);
  Lean's kernel holds it (groups_W). -/
def armAW : Params.ForestSize × Params.AttentionRounds × Params.SmallSize :=
  ({ v := 29, d := 18, shifted := true },
   { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14, 20)], e
       := 13,
     valueM := 16, valueD := 13, attained := 20, bits := 17, rows := 14166783 },
   { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } })

/-- A plan's three values are a. -/
def armIs (a : Params.ForestSize × Params.AttentionRounds × Params.SmallSize) (X : Attention.Plan) :
    Bool :=
  decide ((forestSize X.fs, X.own, smallSize X.seam.tl) = a)

/-- Each of the twelve groups' twins returns, and its three values are a. -/
def groupsOK (a : Params.ForestSize × Params.AttentionRounds × Params.SmallSize) : Bool :=
  withLookC fun y => onOk (Layer.scalesOf hW scalesF.toArray) fun s =>
    onOk (Attention.readLines PW.polCallsA) fun l => (List.range 12).all fun g =>
      onOk (Attention.groupS (some refL.toArray) PW y s (mqOf y) l g) (armIs a)

/-! ## Closed facts: Lean's kernel evaluates them -/

/-- **The certificate accepts** at the scan's written value, the first half of the layers' layout
  there, and the scales
off the written list of the scale file's words: all twelve groups. -/
theorem attB_W : onOk (baseNoFill hW callsRef) (fun y0 => onOk (Layer.scalesOf hW scalesF.toArray)
    fun s =>
    attB (some refL.toArray) 4096 PW y0 s) = true := by decide +kernel

/-- **Each of the twelve groups' twins returns with the written arm**, at a layout of the form that
  layoutLook returns. -/
theorem groups_W : groupsOK armAW = true := by decide +kernel

/-- A negative test, stated positively: with one row more in the written arm the same test says no.
  -/
theorem groups_W_no : groupsOK (armAW.1, { armAW.2.1 with rows := armAW.2.1.rows + 1 }, armAW.2.2) =
    false := by
  decide +kernel

/-- The first half of the layers' layout has twelve groups. -/
theorem twelve_W : onOk (baseNoFill hW callsRef) (fun y0 => y0.NGr == 12) = true := by
  decide +kernel

/-- configO's two tests on the parameter file's numbers do not refuse. -/
theorem front1 : (PW.h.Gk &&& (PW.h.Gk - 1) != 0) = false := by decide +kernel
theorem front2 : (decide (PW.h.lmh < PW.h.lt) || decide (PW.h.lmh > 24) || decide (PW.h.lmo <
    PW.h.lt) ||
    decide (PW.h.lmo > 24) || decide (PW.h.lmbA > 24) || decide (PW.h.lmS > 24) || PW.h.NAs == 0 ||
    decide (PW.h.NAs > 64)) = false := by decide +kernel

/-! ## The joinings -/

/-- The certificate reads none of the three fields. -/
theorem attB_look (tt : Option (Array Nat)) (M : Nat) (P : PolScan) (y0 : Lay) (cl : Array Call)
    (fo : Forest.Shape) (kbm : Nat) (s : Layer.Scales) :
    attB tt M P (lookAt y0 cl fo kbm) s = attB tt M P y0 s := rfl

/-- **At the written values the attention's configuration is its twin**: at all hashes o, all
  numberings mq, and whatever
the three fields that layoutLook sets. -/
theorem config_twin (o : Nat → ByteArray → ByteArray) {y0 : Lay} {s : Layer.Scales}
    (hy : baseNoFill hW callsRef = .ok y0) (hs : Layer.scalesOf hW scalesF.toArray = .ok s)
    (cl : Array Call) (fo : Forest.Shape) (kbm : Nat) (mq : Nat → Nat) :
    configO o PW (lookAt y0 cl fo kbm) s mq =
      configS (some refL.toArray) o PW (lookAt y0 cl fo kbm) s mq :=
  config_of_check o PW _ s mq (by
    rw [attB_look]
    have h1 := onOk_ok attB_W hy
    have h2 := onOk_ok h1 hs
    exact h2)

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem refuse_false (n : String) : refuseIf false n = .ok () := rfl

/-- Where the function returns at every member, with a property, mapM returns a list of that length
  whose members have it. -/
theorem mapM_of_each {α β : Type} {f : α → Except String β} {Q : β → Prop} :
    ∀ l : List α, (∀ a ∈ l, ∃ b, f a = .ok b ∧ Q b) →
      ∃ bs, l.mapM f = .ok bs ∧ bs.length = l.length ∧ ∀ b ∈ bs, Q b
  | [], _ => ⟨[], by rw [List.mapM_nil]; rfl, rfl, fun b hb => by cases hb⟩
  | a :: l, h => by
    obtain ⟨b, hb, qb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs, hl, hq⟩ := mapM_of_each l fun c hc => h c (List.mem_cons_of_mem _ hc)
    refine ⟨b :: bs, ?_, by rw [List.length_cons, List.length_cons, hl], ?_⟩
    · rw [List.mapM_cons, hb, hbs]
      rfl
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact qb
      · exact hq c hc

/-- The table of exponentials in a plan that group returns at a configuration with S = 12, rx = 8 is
  the library's list. -/
theorem group_Tt {P : PolScan} {y : Lay} {s : Layer.Scales} {mq : Nat → Nat} {l : List
    Attention.Line}
    {g : Nat} {X : Attention.Plan} (h : Attention.group P y s mq l g = .ok X)
    (hc : ∀ cf, Attention.fill P y s l g = .ok cf → cf.S = 12 ∧ cf.rx = 8) : X.S.Tt = refL.toArray
        := by
  obtain ⟨cf, hf, hS, -, -⟩ := OnBytes.Road.L5.shaped_of_group h
  obtain ⟨a, b⟩ := hc cf hf
  have e := hS.exp
  rw [a, b, expTable_W] at e
  exact (Option.some.inj e).symm

/-- **THE ATTENTION's CONFIGURATION RETURNS AT THE WRITTEN VALUES, if the digest of the library's
  table of exponentials is
the parameter file's**: and what it returns: twelve plans, each what the group's twin returns, of
  each of which the attention's arm
reads the written armAW, and the digest of the four lines. -/
theorem config_returns (o : Nat → ByteArray → ByteArray) {y0 : Lay} {fo : Forest.Shape} {kbm : Nat}
    {s : Layer.Scales} (hy : baseNoFill hW callsRef = .ok y0)
    (hf : Forest.shapeNoAsk (clOf y0) y0.h.lidb = .ok fo) (hk : Forest.planeCols fo y0.h.lmb = .ok
        kbm)
    (hs : Layer.scalesOf hW scalesF.toArray = .ok s)
    (hT : tableHeldO o PW .exp refL.toArray = .ok ()) :
    ∃ (l : List Attention.Line) (ps : List Attention.Plan),
      Attention.readLines PW.polCallsA = .ok l ∧
      (List.range 12).mapM (Attention.groupS (some refL.toArray) PW (lookC y0 fo kbm) s
        (mqOf (lookC y0 fo kbm)) l) = .ok ps ∧
      ps.length = 12 ∧ (∀ X ∈ ps, armIs armAW X = true) ∧
      configO o PW (lookC y0 fo kbm) s (mqOf (lookC y0 fo kbm)) =
        .ok { plans := ps.toArray, hCallsA := callsDigestO o l } := by
  have hN : (lookC y0 fo kbm).NGr = 12 := by
    have h := onOk_ok twelve_W hy
    exact beq_iff_eq.mp h
  have hA : attB (some refL.toArray) 4096 PW (lookC y0 fo kbm) s = true := by
    unfold lookC
    rw [attB_look]
    have h1 := onOk_ok attB_W hy
    have h2 := onOk_ok h1 hs
    exact h2
  have g0 := groups_W
  unfold groupsOK withLookC at g0
  have g1 := onOk_ok g0 hy
  have g2 := onOk_ok g1 hf
  have g3 := onOk_ok g2 hk
  have g4 := onOk_ok g3 hs
  obtain ⟨l, hl, g5⟩ := onOk_ex g4
  have each : ∀ g ∈ List.range 12, ∃ X, Attention.groupS (some refL.toArray) PW (lookC y0 fo kbm) s
      (mqOf (lookC y0 fo kbm)) l g = .ok X ∧ (armIs armAW X = true ∧ X.S.Tt = refL.toArray) := by
    intro g hg
    have g6 := List.all_eq_true.mp g5 g hg
    obtain ⟨X, hX, aX⟩ := onOk_ex g6
    have hg' : g ∈ List.range (lookC y0 fo kbm).NGr := by rw [hN]; exact hg
    have hc := att_at hA hl hg'
    refine ⟨X, hX, aX, group_Tt (mq := mqOf (lookC y0 fo kbm)) (g := g) ?_ fun cf hcf => (hc cf
        hcf).1⟩
    rw [group_eq (some refL.toArray) PW _ s _ l g fun cf hcf => (hc cf hcf).2]
    exact hX
  obtain ⟨ps, hps, hlen, hq⟩ := mapM_of_each _ each
  refine ⟨l, ps, hl, hps, by rw [hlen, List.length_range], fun X hX => (hq X hX).1, ?_⟩
  rw [config_of_check o PW _ s _ hA]
  cases ps with
  | nil =>
    rw [List.length_range] at hlen
    cases hlen
  | cons X rest =>
    have hX : X.S.Tt = refL.toArray := (hq X (List.mem_cons_self ..)).2
    unfold configS
    simp only [hl, ok_bind, front1, front2, refuse_false, hN, hps, hX, hT]
    rfl

end OnBytes.Road.K4.Trial.AttAtW

#print axioms OnBytes.Road.K4.Trial.AttAtW.attB_W
#print axioms OnBytes.Road.K4.Trial.AttAtW.groups_W
#print axioms OnBytes.Road.K4.Trial.AttAtW.groups_W_no
#print axioms OnBytes.Road.K4.Trial.AttAtW.twelve_W
#print axioms OnBytes.Road.K4.Trial.AttAtW.front1
#print axioms OnBytes.Road.K4.Trial.AttAtW.front2
#print axioms OnBytes.Road.K4.Trial.AttAtW.attB_look
#print axioms OnBytes.Road.K4.Trial.AttAtW.config_twin
#print axioms OnBytes.Road.K4.Trial.AttAtW.mapM_of_each
#print axioms OnBytes.Road.K4.Trial.AttAtW.group_Tt
#print axioms OnBytes.Road.K4.Trial.AttAtW.config_returns
