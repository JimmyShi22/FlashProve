-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TieReads.lean: THE TWELVE TABLES OF THE OUTPUT HEAD's READS, ONE BY ONE, OVER THE SMALLNESS TEST's TIE: where the tie holds (TieOf, Johnson/Desc/First/K8/LawItems.lean: for every table of the record's closed list the read's cell is the sum, under the table's weights, of the committed integers), EACH
ENTRY OF EACH OF THE TWELVE TABLES THAT THE KIND's FORMS CAN NAME IS WORTH OUR READ IN TRUTH (readAt | readAtN) AT ANY RECORD OF CELLS WHOSE IMAGES ARE THE COMMITTED ENTRIES: STATED AND PROVED.
THE FIND. The tie's third clause IS, to the letter, the sentence Holds (Johnson/Road/FormsKeysMat.lean:88) for every table of the list, at the matrices' entries M μ i c := the image of the committed integer a μ i c, once the world's entry of the reads' array at (pos / K3, pos % K3) is the tie's cell (the reads' array, 0,
pos). So the two roads to "the sent reads are the true ones" (the tie; TrueH) ARE ONE: the tie gives Holds (holds_of_tie), Holds gives TrueH (trueH_of_holds), TrueH gives the twelve (twelve_of_trueH).
  TieThird        the tie's third clause, SPELLED HERE AS A PREMISE, letter for letter: LawTie.lean and what it imports are not in this file's reach: NO SECOND DEFINITION IS MEANT: whoever can import both states the equation by rfl.
  CellsAre c t    the images in the field of c's cells are the entries t (the library's record of the head's cells: hf hd hr x): wide | hf · act | hd · row | hr · stream | x, feature for feature, position for position. GENERAL IN c: it is met by cellsH (adrOf h L b) μ where the entries are
                  images of integers below 2^18 in size, and by the committed integers themselves (cellsAre_int). THE TIE's BOUND IS THAT BOUND: below twice the shift = 2 · 2^17 (OnBytes/Model/Frame.lean:229).
  EntryIs         the table with this name: each entry that the forms can name is worth rd of (v e).
  TwelveTrue      the twelve, each at THE RUN's OWN WEIGHTS in our words: six short tables at eq of the run's point · two at the run's vectors of the positions with a cost · four long ones at eq · eq of the run's point cut in two, or 1 · the cost's vector.
  holds_of_tie · cellsAre_int · short_eq | short_vec | long_eq · twelve_of_trueH · trueH_of_tie · twelve_of_tie
WHAT IT DOES NOT SAY. **THAT THE RUN's POINTS AND VECTORS ARE OUR LETTERS** (zt, zl, pV, the sumchecks' challenges, phiC, the count's weights): the twelve speak of R.x's fields: the tie to the kind's classes at the seat (HeadSeat.lean's allOf | heardOf) IS NOT TYPED. THAT OUR NUMBER OF A FEATURE IS THE LIBRARY's: CellsAre takes it so. The points'
sizes are premises in the fields that need them. trueH_of_tie | twelve_of_tie stand AT THE FULL SIZE ALONE (FullH, NumH, BorderH are among their premises) and ask that the run's tables are the record's closed list (hfuns), that planH2 | tablesOf return, and that the world's entries of the reads' array are the tie's cells (hW: one row, K3 columns at
least the vector's length, is what makes it so: not shown). The tie itself is a premise (k08_row closes it). Nothing on the three tables of the planes (Law/HeadPlanes.lean). Valid e: the entry lies below its table's length: beyond it nothing is said. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Reading World HFun HTailF2 lastOf cutLast longPoint)
open OnBytes.Model.Head (costWeights ztOf zjOf callNo)
open OnBytes.Road (Mats Holds)
open OnBytes.Road.Hd (SumShort SumLong Starts Valid rdW TrueH cellsH)
open Norm (lt ls d lPd S2 T)

/-- The smallness test's tie, its third clause, letter for letter (u3: the reads' array; A: the table of cells; a: the committed integers). -/
def TieThird (tl : HTailF2) (u3 : Nat) (A : Nat → Nat → Nat → K) (a : Nat → Nat → Nat → Int) : Prop :=
  ∀ (n : Nat) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
    A u3 0 pos =
      ∑ j ∈ Finset.range Fn.len,
        Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : Int) : K)

/-- The images in the field of c's cells are the entries t. -/
def CellsAre (c : NCells) (t : Inst.Model.Head.Cells K) : Prop :=
  (∀ f i, ((c.cell .wide f i : Int) : K) = t.hf f i) ∧
  (∀ f i, ((c.cell .act f i : Int) : K) = t.hd f i) ∧
  (∀ f i, ((c.cell .row f i : Int) : K) = t.hr f i) ∧
  (∀ f i, ((c.stream f i : Int) : K) = t.x f i)

/-- The table with the name nm: each entry that the forms can name is worth rd of (v e). -/
def EntryIs (W : World K) (R : OnBytes.Model.Head.Run) (K3 : Nat) (nm : String) (v : Nat → E) : Prop :=
  ∀ tb, Starts R nm tb → ∀ e, Valid R tb e → rdW W R.iU3 K3 (tb + e) = rd (v e)

variable [Sizes]

/-- **THE TWELVE TABLES, EACH WORTH OUR READ IN TRUTH AT THE RUN's OWN WEIGHTS.** -/
structure TwelveTrue (W : World K) (R : OnBytes.Model.Head.Run) (K3 : Nat) (c : NCells) : Prop where
  hfZ : R.x.Zl.size = ls + lt → EntryIs W R K3 "hf@Z"
    (readAt c.toCells (.wide, .long (eq (R.x.Zl.extract 0 ls)) (eq (R.x.Zl.extract ls (ls + lt)))))
  hfPhiZ : EntryIs W R K3 "hf@phiZ" (readAt c.toCells (.wide, .long (fun _ => 1)
    fun i => (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD i zeroE))
  xZV : ∀ ZV, lastOf R.x.wpl.r R.h.la = .ok ZV → ZV.size = ls + lt → EntryIs W R K3 "xbL@Z_V"
    (readAtN c (.stream, .long (eq (ZV.extract 0 ls)) (eq (ZV.extract ls (ls + lt)))))
  xYN : ∀ lowN, cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls = .ok lowN →
    (longPoint lowN.2 R.x.tN.r).size = ls + lt → EntryIs W R K3 "xbL@Y_N"
    (readAtN c (.stream, .long (eq ((longPoint lowN.2 R.x.tN.r).extract 0 ls))
      (eq ((longPoint lowN.2 R.x.tN.r).extract ls (ls + lt)))))
  hdFC : ∀ q, callNo R.L "CNF" = some q → (ztOf R.h R.L R.x.g1 q).size = lt →
    EntryIs W R K3 "hd@zt_FC" (readAt c.toCells (.act, .short (eq (ztOf R.h R.L R.x.g1 q))))
  hdRH : R.x.tH.r.size = lt → EntryIs W R K3 "hd@r_H" (readAt c.toCells (.act, .short (eq R.x.tH.r)))
  hrROW : ∀ q, callNo R.L "ROW" = some q → (ztOf R.h R.L R.x.g1 q).size = lt →
    EntryIs W R K3 "hr@zt_ROW" (readAt c.toCells (.row, .short (eq (ztOf R.h R.L R.x.g1 q))))
  hrPV : R.x.PV.size = lt → EntryIs W R K3 "hr@P_V" (readAt c.toCells (.row, .short (eq R.x.PV)))
  hrTV : R.x.tV.r.size = lt → EntryIs W R K3 "hr@r_tV" (readAt c.toCells (.row, .short (eq R.x.tV.r)))
  hrTN : R.x.tN.r.size = lt → EntryIs W R K3 "hr@rt_N" (readAt c.toCells (.row, .short (eq R.x.tN.r)))
  hrPhiC : EntryIs W R K3 "hr@phiC" (readAt c.toCells (.row, .short
    fun i => (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD i zeroE))
  hrRhoC : EntryIs W R K3 "hr@rhoC" (readAt c.toCells (.row, .short
    fun i => (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2.getD i zeroE))

namespace Came

omit [Sizes] in
/-- **The tie gives Holds, for every table of the closed list.** -/
theorem holds_of_tie {tl : HTailF2} {u3 : Nat} {A : Nat → Nat → Nat → K} {a : Nat → Nat → Nat → Int}
    (hT : TieThird tl u3 A a) {W : World K} {iU3 K3 : Nat}
    (hW : ∀ pos, W.entry iU3 (pos / K3) (pos % K3) = A u3 0 pos) :
    ∀ Fn ∈ tl.funs, Holds Reading.gl W tl iU3 K3 (fun μ i c => ((a μ i c : Int) : K)) Fn := by
  intro Fn hFn c sg pos hp
  obtain ⟨n, hn⟩ := Array.mem_iff_getElem?.mp hFn
  rw [hW]
  exact hT n Fn hn c sg pos hp

omit [Sizes] in
/-- The committed integers, read by the map of cells, are cells whose images are the entries. -/
theorem cellsAre_int (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) (a : Nat → Nat → Nat → Int) (c : NCells)
    (h1 : ∀ f i, c.cell .wide f i = (cellsH h L b a).hf f i)
    (h2 : ∀ f i, c.cell .act f i = (cellsH h L b a).hd f i)
    (h3 : ∀ f i, c.cell .row f i = (cellsH h L b a).hr f i)
    (h4 : ∀ f i, c.stream f i = (cellsH h L b a).x f i) :
    CellsAre c (cellsH h L b fun μ i k => ((a μ i k : Int) : K)) :=
  ⟨fun f i => by rw [h1]; rfl, fun f i => by rw [h2]; rfl, fun f i => by rw [h3]; rfl,
    fun f i => by rw [h4]; rfl⟩

/-- A short table at eq of a point of lt coordinates. -/
theorem short_eq {W : World K} {R : OnBytes.Model.Head.Run} {K3 : Nat} {nm : String} {z : Point}
    {cell : Nat → Nat → K} {cz : Nat → Nat → Int} (hcz : ∀ e i, ((cz e i : Int) : K) = cell e i)
    (hT : R.h.T = T) (hz : z.size = lt)
    (h : SumShort Reading.gl W R K3 nm (OnBytes.Model.eqTab z) cell) :
    EntryIs W R K3 nm fun e => sumTo T fun i => eq z i * ofInt (cz e i) :=
  short_meets hcz (eq z) hT (fun i hi => eqTab_reads z i (by rw [hz]; exact hi)) h

/-- A short table at a vector of weights. -/
theorem short_vec {W : World K} {R : OnBytes.Model.Head.Run} {K3 : Nat} {nm : String} {phi : Array E}
    {cell : Nat → Nat → K} {cz : Nat → Nat → Int} (hcz : ∀ e i, ((cz e i : Int) : K) = cell e i)
    (hT : R.h.T = T) (h : SumShort Reading.gl W R K3 nm phi cell) :
    EntryIs W R K3 nm fun e => sumTo T fun i => phi.getD i zeroE * ofInt (cz e i) :=
  short_meets hcz (fun i => phi.getD i zeroE) hT (fun _ _ => rfl) h

/-- A long table at a point of ls + lt coordinates. -/
theorem long_eq {W : World K} {R : OnBytes.Model.Head.Run} {K3 : Nat} {nm : String} {Z : Point}
    {cell : Nat → Nat → K} {cz : Nat → Nat → Int} (hcz : ∀ e i, ((cz e i : Int) : K) = cell e i)
    (hT : R.h.T = T) (hS : R.h.S2 = S2) (hZ : Z.size = ls + lt)
    (h : SumLong Reading.gl W R K3 nm (OnBytes.Model.longPhi Z ls lt) cell) :
    EntryIs W R K3 nm fun e => sumTo S2 fun j => sumTo T fun i =>
      eq (Z.extract 0 ls) j * eq (Z.extract ls (ls + lt)) i * ofInt (cz (S2 * e + j) i) :=
  long_meets hcz _ _ hT hS (fun _ _ hr hi => longPhi_cut Z ls lt hZ hr hi) h

/-- **TrueH gives the twelve, at any cells whose images are the entries.** -/
theorem twelve_of_trueH {W : World K} {R : OnBytes.Model.Head.Run} {K3 : Nat}
    {t : Inst.Model.Head.Cells K} {c : NCells} (hc : CellsAre c t) (hlt : R.h.lt = lt)
    (hls : R.h.ls = ls) (hla : R.h.la = ls + lt) (H : TrueH Reading.gl W R K3 t) :
    TwelveTrue W R K3 c := by
  have hT : R.h.T = T := by
    show 2 ^ R.h.lt = 2 ^ lt
    rw [hlt]
  have hS : R.h.S2 = S2 := by
    show 2 ^ R.h.ls = 2 ^ ls
    rw [hls]
  obtain ⟨c1, c2, c3, c4⟩ := hc
  refine ⟨fun hZ => ?_, ?_, fun ZV hv hZ => ?_, fun lowN hl hZ => ?_, fun q hq hz => ?_,
    fun hz => ?_, fun q hq hz => ?_, fun hz => ?_, fun hz => ?_, fun hz => ?_, ?_, ?_⟩
  · have h := H.hfZ
    rw [hls, hlt] at h
    exact long_eq c1 hT hS hZ h
  · refine long_meets c1 (fun _ => 1) _ hT hS (fun r i hr hi => ?_) H.hfPhiZ
    have hlt2 : r * T + i < 2 ^ R.h.la := by
      rw [hla, pow_add]
      have h1 : r * T + i < (r + 1) * T := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right T hr)
    have hm : (r * T + i) % R.h.T = i := by
      rw [hT, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    rw [rd_one, one_mul]
    congr 1
    simp [Array.getD, hlt2, hm]
  · have h := H.xZV ZV hv
    rw [hls, hlt] at h
    exact long_eq c4 hT hS hZ h
  · have h := H.xYN lowN hl
    rw [hls, hlt] at h
    exact long_eq c4 hT hS hZ h
  · exact short_eq c2 hT hz (H.hdFC q hq)
  · exact short_eq c2 hT hz H.hdRH
  · exact short_eq c3 hT hz (H.hrROW q hq)
  · exact short_eq c3 hT hz H.hrPV
  · exact short_eq c3 hT hz H.hrTV
  · exact short_eq c3 hT hz H.hrTN
  · exact short_vec c3 hT H.hrPhiC
  · exact short_vec c3 hT H.hrRhoC

open OnBytes.Model (Fork Settings) in
open OnBytes.Model.Head (Owner HPlanH2 planH2 tablesOf) in
open OnBytes.Road.Hd (FullH NumH BorderH) in
omit [Sizes] in
/-- **THE TIE GIVES TrueH**, at the full size, at its own premises on the run, at the images of the committed integers. -/
theorem trueH_of_tie {R : OnBytes.Model.Head.Run} {g : Settings} {O : Owner} {NGr lkW : Nat}
    {H0 : HPlanH2} (hpl : planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (hF : FullH R.h)
    (N : NumH R.h R.L) (Bd : BorderH R.b) {F G : Fork} {C D : OnBytes.Ctx}
    (ht : OnBytes.Road.Hd.Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {tl : HTailF2}
    (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) (hfuns : R.t.funs = tl.funs)
    {u3 K3 : Nat} {A : Nat → Nat → Nat → K} {a : Nat → Nat → Nat → Int} (hT : TieThird tl u3 A a)
    {W : World K} (hW : ∀ pos, W.entry R.iU3 (pos / K3) (pos % K3) = A u3 0 pos) :
    TrueH Reading.gl W R K3 (cellsH R.h R.L R.b fun μ i k => ((a μ i k : Int) : K)) :=
  OnBytes.Road.Hd.trueH_of_holds hpl hm0 hN0 hF N Bd ht hm hNM
    (by rw [hfuns]; exact holds_of_tie hT hW)

open OnBytes.Model (Fork Settings) in
open OnBytes.Model.Head (Owner HPlanH2 planH2 tablesOf) in
open OnBytes.Road.Hd (FullH NumH BorderH) in
/-- **THE TIE GIVES THE TWELVE**, at the full size, at TrueH's own premises on the run. -/
theorem twelve_of_tie {R : OnBytes.Model.Head.Run} {g : Settings} {O : Owner} {NGr lkW : Nat}
    {H0 : HPlanH2} (hpl : planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (hF : FullH R.h)
    (N : NumH R.h R.L) (Bd : BorderH R.b) {F G : Fork} {C D : OnBytes.Ctx}
    (ht : OnBytes.Road.Hd.Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {tl : HTailF2}
    (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) (hfuns : R.t.funs = tl.funs)
    {u3 K3 : Nat} {A : Nat → Nat → Nat → K} {a : Nat → Nat → Nat → Int} (hT : TieThird tl u3 A a)
    {W : World K} (hW : ∀ pos, W.entry R.iU3 (pos / K3) (pos % K3) = A u3 0 pos) {c : NCells}
    (hc : CellsAre c (cellsH R.h R.L R.b fun μ i k => ((a μ i k : Int) : K)))
    (hlt : R.h.lt = lt) (hls : R.h.ls = ls) (hla : R.h.la = ls + lt) : TwelveTrue W R K3 c :=
  twelve_of_trueH hc hlt hls hla
    (trueH_of_tie hpl hm0 hN0 hF N Bd ht hm hNM hfuns hT hW)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.holds_of_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.twelve_of_trueH
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.trueH_of_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.twelve_of_tie
