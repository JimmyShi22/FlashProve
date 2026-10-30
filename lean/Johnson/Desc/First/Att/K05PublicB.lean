-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PublicB.lean: K5Public (Att/K05LawOne.lean: the thirteen tests on public
data that kind K5's law in one statement takes) AS ONE BOOLEAN THAT A PROGRAM CAN RUN, with the
lemma that makes a run's "true" spendable.

Main names:
  `attOKB`, `attOK_of_yes`: AttOK (Look/K3CallerAtt.lean: five tests; none reads tl, D or rad).
  `matsFitB`, `matsFit_of_yes`: MatsFit (Johnson/Road/Rows/AttRead.lean). `plainB`, `plain_of_yes`:
    Plain (OnBytes/Tie/Pv/Lookup/Forest/FoPeelMeets.lean).
  `k5PublicAtB`: the conjunction of TWELVE of the thirteen, field for field, at a plan record A.
    `k5Public_of_yes`: with "A is the planner's return" it gives K5Public. `k5PublicCoreAtB`,
    `k5PublicAtB_core` (by rfl), `k5PublicAtB_congr`: OF THE SETTING AND THE PLACE x THE TWELVE
    READ FIVE THINGS: the shape that the kind's own parameters make of the place, x.fs, x.lm,
    x.F.next, x.ns: so two sets of letters that agree in these, in (settings, inp, cf), in p, ds and
    kc have one verdict.
  `k5PublicB`: ALL THIRTEEN: A := WHAT THE PLANNER RETURNS, computed; the letters that hang on A are
    handed in as functions of it. `k5Public_of_run`: a yes gives an A with Attention.plan's return
    and K5Public.
  `claims_of_atO`: WHENCE THE DRY RUN's LETTERS: at tl := A.seam.tl, iU3 := A.iU3, nW := A.nW, Kc :=
    the planned ledger's number of columns at that tree, k3 := padOfO A.fs, nzx := A.fs.dT, the
    field "claims" is the block's own test claimsOkAtO A (Att/SeatO.lean), where the planes' test
    says yes.
  `pairs_of_planOk`, `pair_of_planOk`: the kind's own test on the plan gives "there is a pair".
  `k5PublicSeatB`, `k5Public_of_seat`: k5PublicB at that filling, at the place's numbers ⟨link,
    piece, work, own, before⟩ and a stretch that may hang on them.
  `k5PublicWrittenB`, `k5Public_of_written`: the same at ds := written p, where the three tests on
    the stretch are theorems (Att/K05Seam.lean) and are not run.

WHICH OF THE THIRTEEN A RUNNING TEXT ASKS TODAY. The blocks k5AtU
(Att/SeatU.lean [not in this library]) and k5AtO
(Att/SeatO.lean) bear the test planOk p && claimsOkAtO a on the plan. From it: "claims"
(claims_of_atO, beside "planes" and "fs") and "pair" (pair_of_planOk, beside "plan", "planOk" and
"own"). By the make of the block's numbers: "own", where a is A. ASKED BY NO RUNNING TEXT OF K5's
FILES: "att" (five tests) · "fs" · "planOk" (planOkAll) · "mats" · "planes" as such (claimsOkAtO
hands it into the dry run, whose tables' routine refuses at false: by reading, Att/TablesP.lean; not
typed) · "held" · "plan" as a test · "plain", "entries", "kinds" (they speak of a description's
data). Whether a chain's fold tests a block's planOk before it puts out is not looked at here. THE
FIELD "plan" IS NO BOOLEAN AT A LETTER A: "= .ok A" wants a decision of equality of plan records. So
it is read: A is computed. At a public record whose group's plan record is a, run it at (a.settings,
a.inp, a.S.cf) with own := a.own: the field "own" then tests a.own = A.own: that a itself is the
planner's return is not needed. THREE INSTANCES stand in this file, in its own namespace PublicB:
DecidableEq for Model.Call, Model.Forest.Shape and Params.AttentionRounds (derived).
Limits. EVALUATED IS NOT PROVED: a run of Lean's evaluator that prints "true" is no kernel proof of
the premise of k5Public_of_run; it is a print. No value of any of these Booleans is stated here.
Each can be false. What stands beside the law and is no field (the guards of the caller's reading;
the packing) is no conjunct here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LawOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P.PublicB

deriving instance DecidableEq for OnBytes.Model.Call
deriving instance DecidableEq for OnBytes.Model.Forest.Shape
deriving instance DecidableEq for OnBytes.Params.AttentionRounds

end VerifiableInference.Desc.First.Att.P.PublicB

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent AttOK attFitsB)
open PublicB

/-! ## The parts -/

/-- AttOK's five tests. -/
def attOKB (set : Params.Setting) (x : VerifiableInference.Desc.First.Look.Place)
    (S : Attention.Shape) : Bool :=
  Decidable.decide ((VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape = some x.fs) &&
    Decidable.decide (x.fs.NC = 4) && (Forest.planeCols x.fs x.lm).toBool && attFitsB S x.fs &&
    Decidable.decide (x.F.next + FoNums.nMasks x.fs ≤ x.ns)

theorem attOK_of_yes {set : Params.Setting} {x : VerifiableInference.Desc.First.Look.Place}
    {S : Attention.Shape} (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (h : attOKB set x S = true) : AttOK set x S tl D rad := by
  unfold attOKB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- MatsFit's five tests. -/
def matsFitB (S : Attention.Shape) (tl : HTailF2) : Bool :=
  Decidable.decide (tl.NM = S.cf.NAs + 4) &&
    (List.range S.cf.NAs).all (fun q => Decidable.decide ((tl.mats.getD q {}).m = 2 ^ S.cf.lmS) &&
      Decidable.decide ((tl.mats.getD q {}).k = S.kAs / S.cf.NAs)) &&
    Decidable.decide ((tl.mats.getD S.cf.NAs {}).m = S.cf.wcH * S.T) &&
    Decidable.decide ((tl.mats.getD (S.cf.NAs + 1) {}).m = S.cf.wcO * S.T) &&
    Decidable.decide ((tl.mats.getD (S.cf.NAs + 3) {}).m = S.cf.wcQ * S.T)

theorem matsFit_of_yes {S : Attention.Shape} {tl : HTailF2} (h : matsFitB S tl = true) :
    OnBytes.Road.Rows.MatsFit S tl := by
  unfold matsFitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Plain's eight tests. -/
def plainB (d : PQ.RD) : Bool :=
  d.items.all (fun it => Decidable.decide (it = Fmt.Item.e)) && Decidable.decide (d.items.length = d.entry.msg / 24) &&
    Decidable.decide (d.entry.poss = 0) && Decidable.decide (d.entry.logN = 0) && Decidable.decide (d.entry.trits = 0) &&
    Decidable.decide (d.kind ≠ .sealed) && Decidable.decide (d.kind ≠ .seeds) &&
    Decidable.decide (d.entry.drawNZ ≤ d.entry.drawE)

theorem plain_of_yes {d : PQ.RD} (h : plainB d = true) : Plain d := by
  unfold plainB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Twelve fields at a plan record -/

/-- **Twelve of K5Public's thirteen fields**, in its order, at a plan record A. -/
def k5PublicAtB (set : Params.Setting) (cf : Attention.Cfg)
    (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (A : Attention.Plan) (p : Par)
    (ds : List RDT) (kc iU3 nW Kc : ℕ) (k3 : Runs.PadIn) (nzx : ℕ) : Bool :=
  attOKB set x A.S && Decidable.decide (x.fs = A.fs) && planOkAll cf A.S A.fs && Decidable.decide (p.own = A.own) &&
    Decidable.decide ((dimOf A.S).nb ≠ 0) && matsFitB A.S tl &&
    claimsOk ⟨geoOf A.S, iU3, nW, K5Law.matsOf tl.mats⟩ Kc k3 true nzx &&
    Look.planesOk x.fs (parCOf A).geo.lmb && ds.all (fun d => plainB (toRD d)) &&
    Decidable.decide (ds.map (·.entry) = (rounds p).map (·.entry)) &&
    ds.all (fun d => Decidable.decide (Fmt.kindOf d.entry.name = some d.kind)) &&
    k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry))

/-- The same text with, in the place of the setting and the lookup's place x, THE FIVE THINGS THAT
IT READS OF
THEM: made: the shape that the kind's own parameters make of the place; x.fs; x.lm; x.F.next; x.ns.
-/
def k5PublicCoreAtB (made : Option Forest.Shape) (fs : Forest.Shape) (lm next ns : ℕ)
    (cf : Attention.Cfg) (tl : HTailF2) (A : Attention.Plan) (p : Par) (ds : List RDT)
    (kc iU3 nW Kc : ℕ) (k3 : Runs.PadIn) (nzx : ℕ) : Bool :=
  (Decidable.decide (made = some fs) && Decidable.decide (fs.NC = 4) &&
      (Forest.planeCols fs lm).toBool && attFitsB A.S fs &&
      Decidable.decide (next + FoNums.nMasks fs ≤ ns)) &&
    Decidable.decide (fs = A.fs) && planOkAll cf A.S A.fs && Decidable.decide (p.own = A.own) &&
    Decidable.decide ((dimOf A.S).nb ≠ 0) && matsFitB A.S tl &&
    claimsOk ⟨geoOf A.S, iU3, nW, K5Law.matsOf tl.mats⟩ Kc k3 true nzx &&
    Look.planesOk fs (parCOf A).geo.lmb && ds.all (fun d => plainB (toRD d)) &&
    Decidable.decide (ds.map (·.entry) = (rounds p).map (·.entry)) &&
    ds.all (fun d => Decidable.decide (Fmt.kindOf d.entry.name = some d.kind)) &&
    k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry))

/-- **What the twelve read of the setting and of the place**: five things. -/
theorem k5PublicAtB_core (set : Params.Setting) (cf : Attention.Cfg)
    (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (A : Attention.Plan) (p : Par)
    (ds : List RDT) (kc iU3 nW Kc : ℕ) (k3 : Runs.PadIn) (nzx : ℕ) :
    k5PublicAtB set cf x tl A p ds kc iU3 nW Kc k3 nzx =
      k5PublicCoreAtB (VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape x.fs x.lm
        x.F.next x.ns cf tl A p ds kc iU3 nW Kc k3 nzx := rfl

/-- **The tie by the letters**: two settings and places with the same five readings have one
verdict, whatever else parts them. -/
theorem k5PublicAtB_congr {set set' : Params.Setting}
    {x x' : VerifiableInference.Desc.First.Look.Place}
    (h1 : (VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape =
      (VerifiableInference.Desc.First.Look.P.ofPlace set' false x').shape)
    (h2 : x.fs = x'.fs) (h3 : x.lm = x'.lm) (h4 : x.F.next = x'.F.next) (h5 : x.ns = x'.ns)
    (cf : Attention.Cfg) (tl : HTailF2) (A : Attention.Plan) (p : Par) (ds : List RDT)
    (kc iU3 nW Kc : ℕ) (k3 : Runs.PadIn) (nzx : ℕ) :
    k5PublicAtB set cf x tl A p ds kc iU3 nW Kc k3 nzx =
      k5PublicAtB set' cf x' tl A p ds kc iU3 nW Kc k3 nzx := by
  rw [k5PublicAtB_core, k5PublicAtB_core, h1, h2, h3, h4, h5]

/-- **A yes is spendable.** -/
theorem k5Public_of_yes {set : Params.Setting} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} (D : Sent)
    (rad : OracleShape → Nat) {A : Attention.Plan} {p : Par} {ds : List RDT} {kc iU3 nW Kc : ℕ}
    {k3 : Runs.PadIn} {nzx : ℕ} (hA : Attention.plan settings i cf = Except.ok A)
    (hu : iU3 = A.iU3) (h : k5PublicAtB set cf x tl A p ds kc iU3 nW Kc k3 nzx = true) :
    K5Public x tl D rad set settings i cf A p ds kc iU3 nW Kc k3 nzx := by
  unfold k5PublicAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨hA, attOK_of_yes tl D rad h1, h2, h3, h4, h5, matsFit_of_yes h6, h7, h8,
    fun d hd => plain_of_yes (h9 d hd), h10, h11, h12, hu⟩

/-! ## All thirteen: the plan record is computed -/

/-- **K5Public as one Boolean.** What hangs on the plan record is handed in as a function of it. -/
def k5PublicB (set : Params.Setting) (settings : Model.Settings) (i : Attention.In)
    (cf : Attention.Cfg) (x : VerifiableInference.Desc.First.Look.Place)
    (tl : Attention.Plan → HTailF2) (p : Attention.Plan → Par) (ds : Attention.Plan → List RDT)
    (kc : ℕ) (iU3 nW Kc : Attention.Plan → ℕ) (k3 : Attention.Plan → Runs.PadIn)
    (nzx : Attention.Plan → ℕ) : Bool :=
  match Attention.plan settings i cf with
  | .ok A => k5PublicAtB set cf x (tl A) A (p A) (ds A) kc (iU3 A) (nW A) (Kc A) (k3 A) (nzx A)
  | .error _ => false

/-- **One "true" gives all thirteen.** -/
theorem k5Public_of_run {set : Params.Setting} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {x : VerifiableInference.Desc.First.Look.Place}
    {tl : Attention.Plan → HTailF2} (D : Sent) (rad : OracleShape → Nat)
    {p : Attention.Plan → Par} {ds : Attention.Plan → List RDT} {kc : ℕ}
    {iU3 nW Kc : Attention.Plan → ℕ} {k3 : Attention.Plan → Runs.PadIn}
    {nzx : Attention.Plan → ℕ} (hu : ∀ A, iU3 A = A.iU3)
    (h : k5PublicB set settings i cf x tl p ds kc iU3 nW Kc k3 nzx = true) :
    ∃ A, K5Public x (tl A) D rad set settings i cf A (p A) (ds A) kc (iU3 A) (nW A) (Kc A) (k3 A)
      (nzx A) := by
  unfold k5PublicB at h
  cases hA : Attention.plan settings i cf with
  | error e => rw [hA] at h; cases h
  | ok A =>
    rw [hA] at h
    exact ⟨A, k5Public_of_yes D rad hA (hu A) h⟩

/-! ## Whence the dry run's letters: the block's own test -/

/-- The planned ledger's number of columns at the tree that holds the tables. -/
def plannedK (A : Attention.Plan) : ℕ := ((A.seam.Fp.trees[A.iU3]?).map (·.K)).getD 0

/-- **The field "claims" at the seat's letters is the block's own test.** -/
theorem claims_of_atO {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan}
    (hfs : x.fs = A.fs) (hpl : Look.planesOk x.fs (parCOf A).geo.lmb = true)
    (h : claimsOkAtO A = true) :
    claimsOk ⟨geoOf A.S, A.iU3, A.nW, K5Law.matsOf A.seam.tl.mats⟩ (plannedK A) (padOfO A.fs) true
      A.fs.dT = true := by
  rw [hfs] at hpl
  unfold claimsOkAtO at h
  have e : Look.planesOk A.fs A.S.cf.lmb = true := hpl
  rw [e] at h
  exact h

/-- The kind's own test on the plan says that there is a pair. -/
theorem pairs_of_planOk {p : Par} (h : planOk p = true) : p.own.pairs ≠ 0 := by
  unfold planOk at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.1.2

/-- **The field "pair" from the block's own test**, beside "plan", "planOk" and "own". -/
theorem pair_of_planOk {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (hA : Attention.plan settings i cf = Except.ok A)
    (hok : planOkAll cf A.S A.fs = true) {p : Par} (hp : p.own = A.own)
    (h : planOk p = true) : (dimOf A.S).nb ≠ 0 := by
  have e := own_recOf x tl D rad ⟨Unit, Unit, Unit, fun _ _ => ()⟩ Unit (fun _ => 0) hA hok p hp 0
    (numsPlan p.own 0)
  have h2 := pairs_of_planOk h
  rw [e] at h2
  exact h2

/-- **K5Public as one Boolean, at the seat's letters.** own: the record of rounds in the block's
numbers. -/
def k5PublicSeatB (set : Params.Setting) (settings : Model.Settings) (i : Attention.In)
    (cf : Attention.Cfg) (x : VerifiableInference.Desc.First.Look.Place) (p : Par)
    (ds : List RDT) (kc : ℕ) : Bool :=
  k5PublicB set settings i cf x (fun A => A.seam.tl) (fun _ => p) (fun _ => ds) kc (fun A => A.iU3)
    (fun A => A.nW) plannedK (fun A => padOfO A.fs) (fun A => A.fs.dT)

theorem k5Public_of_seat {set : Params.Setting} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {x : VerifiableInference.Desc.First.Look.Place} (D : Sent)
    (rad : OracleShape → Nat) {p : Par} {ds : List RDT} {kc : ℕ}
    (h : k5PublicSeatB set settings i cf x p ds kc = true) :
    ∃ A, K5Public x A.seam.tl D rad set settings i cf A p ds kc A.iU3 A.nW (plannedK A)
      (padOfO A.fs) A.fs.dT :=
  k5Public_of_run D rad (fun _ => rfl) h

/-- The ten tests that are left at ds := written p. -/
def k5PublicWrittenB (set : Params.Setting) (settings : Model.Settings) (i : Attention.In)
    (cf : Attention.Cfg) (x : VerifiableInference.Desc.First.Look.Place) (p : Par) (kc : ℕ) :
    Bool :=
  match Attention.plan settings i cf with
  | .ok A => attOKB set x A.S && Decidable.decide (x.fs = A.fs) && planOkAll cf A.S A.fs &&
      Decidable.decide (p.own = A.own) && Decidable.decide ((dimOf A.S).nb ≠ 0) && matsFitB A.S A.seam.tl &&
      claimsOkAtO A && Look.planesOk x.fs (parCOf A).geo.lmb &&
      k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry))
  | .error _ => false

/-- **At the kind's own written rounds**: the three tests on the stretch are theorems, and "claims"
is
the block's own claimsOkAtO. -/
theorem k5Public_of_written {set : Params.Setting} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {x : VerifiableInference.Desc.First.Look.Place} (D : Sent)
    (rad : OracleShape → Nat) {p : Par} {kc : ℕ}
    (h : k5PublicWrittenB set settings i cf x p kc = true) :
    ∃ A, K5Public x A.seam.tl D rad set settings i cf A p (written p) kc A.iU3 A.nW (plannedK A)
      (padOfO A.fs) A.fs.dT := by
  unfold k5PublicWrittenB at h
  cases hA : Attention.plan settings i cf with
  | error e => rw [hA] at h; cases h
  | ok A =>
    rw [hA] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    exact ⟨A, hA, attOK_of_yes _ D rad h1, h2, h3, h4, h5, matsFit_of_yes h6,
      claims_of_atO h2 h8 h7, h8, seam_plain p, seam_entries p, seam_kinds p, h9, rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.attOK_of_yes
#print axioms VerifiableInference.Desc.First.Att.P.matsFit_of_yes
#print axioms VerifiableInference.Desc.First.Att.P.plain_of_yes
#print axioms VerifiableInference.Desc.First.Att.P.k5PublicAtB_core
#print axioms VerifiableInference.Desc.First.Att.P.k5PublicAtB_congr
#print axioms VerifiableInference.Desc.First.Att.P.k5Public_of_yes
#print axioms VerifiableInference.Desc.First.Att.P.k5Public_of_run
#print axioms VerifiableInference.Desc.First.Att.P.claims_of_atO
#print axioms VerifiableInference.Desc.First.Att.P.pair_of_planOk
#print axioms VerifiableInference.Desc.First.Att.P.k5Public_of_seat
#print axioms VerifiableInference.Desc.First.Att.P.k5Public_of_written
