-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Clamp/InsideOfPlan.lean: `InsideAt cs ms own a`
(Johnson/Desc/Sound/Clamp/FormsClamp.lean: "every entry that the open segment's data read lies
inside the ranges of the member at its seat"), FROM THE PROGRAMS' OWN TESTS AND TIES BETWEEN THE
VERIFIER's STATE AND THE LIST OF MEMBERS. Definitions and theorems.

What is said.
  `PartFits cs ms own a`: six clauses, to the letter of a row of a list of this project not in
    this library: the codes; the test on their lengths; the test on the layout; the state's messages
    have the request's shapes; the member at a seat has the state's message's shape; `maskFits`: the
    segment's mask message has a power of two of mask rows and an answer, and the ledger's number of
    slots and the size of its list of coefficients are at most `Send.freeMaskEntries` there.
  `rowBits_mask`, `bits_main`: the statement's bits for a row and a place, at a message's shape.
  `insideAt_main`: **THE FIELD main OF `InsideAt`, TO THE LETTER** (`Meaning.message_of_layout`,
    `block_of_message`, `ell_pow`, Johnson/Goal/Meaning/LaidInside.lean; `inBlock_inside`,
    Clamp/BlockCovers.lean: called).
  `insideAt_mask`: **THE FIELD mask, TO THE LETTER, from the clauses member and maskFits**
    (`Meaning.mask_inside`, Johnson/Goal/Meaning/MaskInside.lean, called at J := j).
  `insideAt_of_fits`: **`InsideAt cs ms own a` from `PartFits cs ms own a`**: the row's theorem.
  `free_one`: at one mask row the ledger gives out "the code's length less the answers" entries.
  `room_of_linksLaid`: **THE BOUND HAS A PAYER IN THE WRITTEN IOP's OWN PUBLIC TEST**: where
    `Ok.Links.linksLaid links codes shape layout` (Johnson/Desc/Ok/Links.lean; the programs':
    OnBytes/Model/StagesLinks.lean, linkLaid: "plan-mask-row") says yes, each link X of the plan has
    `X.ns ≤ Send.freeMaskEntries 1 ell shape.answers`, ell the length of the request's mask code.
  `maskFits_of_plan`: **the clause maskFits** from that test and four ties, each named: the mask
    message's shape has one mask row, the request's mask code and the request's answers; an answer;
    the ledger's number of slots is the plan's X.ns; its list of coefficients is no longer.

Limits. `PartFits`' clauses, and the four ties of `maskFits_of_plan`, are premises: meant at a
reached state of an honest run: shown at no state here. No soundness statement.

-/
import Johnson.Desc.Sound.Clamp.FormsClamp
import Johnson.Desc.Sound.Clamp.BlockCovers
import Johnson.Goal.Meaning.MaskInside
import Johnson.Goal.Meaning.LaidInside
import Johnson.Desc.Ok.Links

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model

section
variable (cs : OnBytes.Codes) (ms : List Mem) (own : List (ℕ × ℕ))

/-- The programs' tests, and the ties between the verifier's state and the list of members. -/
structure PartFits (a : K9.Part) : Prop where
  codes : a.d.st.codes = cs
  lengths : cs.lengthsOk = true
  layoutOk : reqLayoutOk cs a.L.check.frame.shape a.L.check.rows.layout = true
  shapeAt : ∀ born j o m, a.L.check.frame.whereIs born j = some o →
    Meaning.messageAt a.L.check.frame.shape born j = some m →
    (a.d.st.oracles[o]?).map (·.shape) = some m.shape
  member : ∀ o x y sh, (a.d.st.oracles[o]?).map (·.shape) = some sh →
    K9.seatAt own a.d.book o = some x →
    (ms.find? fun y => decide (seatOf y = x)) = some y → (y.1.l.get y.2).1 = sh
  maskFits : ∀ o, K9L.maskOracle a.L.check.frame = some o →
    ∃ sh, (a.d.st.oracles[o]?).map (·.shape) = some sh ∧
      sh.maskRows = 2 ^ ceilLog2 sh.maskRows ∧ 1 ≤ sh.answers ∧
      a.F.ns ≤ Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers ∧
      a.F.LS.size ≤
        Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers

/-- The statement's bits for a mask row. -/
theorem rowBits_mask {St : Statement} {o : ℕ} {sh : OracleShape}
    (h : (St.oracles[o]?).map (·.shape) = some sh) :
    St.rowBits o .mask = ceilLog2 sh.maskRows := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Statement.rowBits
  rw [hx]
  rfl

/-- The statement's bits for a main row and for a place in it. -/
theorem bits_main {St : Statement} {o : ℕ} {sh : OracleShape}
    (h : (St.oracles[o]?).map (·.shape) = some sh) (h0 : sh.mainRows ≠ 0) :
    St.rowBits o .main = ceilLog2 sh.mainRows ∧
      St.placeBits o .main = (St.codes.base.getD sh.code default).logEll := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Statement.rowBits Statement.placeBits
  rw [hx]
  refine ⟨rfl, ?_⟩
  have h1 : (x.shape.rows .main == 0) = false := by
    show (x.shape.mainRows == 0) = false
    simpa using h0
  simp only [h1, Bool.false_eq_true, if_false]

/-- **THE FIELD main OF `InsideAt`.** -/
theorem insideAt_main (a : K9.Part) (F : PartFits cs ms own a) :
    ∀ born name A o b J x y, reqArray a.L.check.rows.layout born name = some A →
      a.L.check.frame.whereIs born A.message = some o → b ∈ A.blocks →
      J < 2 ^ (a.d.st.rowBits o .main + a.d.st.placeBits o .main) →
      (K9L.inBlock b (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) J : GQ) ≠ 0 →
      K9.seatAt own a.d.book o = some x →
      (ms.find? fun y => decide (seatOf y = x)) = some y →
      InMsg cs (y.1.l.get y.2).1 false (J % 2 ^ a.d.st.rowBits o .main)
        (J / 2 ^ a.d.st.rowBits o .main) := by
  intro born name A o b J x y hA ho hb hJ hw hx hy
  obtain ⟨as, hl, hfind⟩ := Option.bind_eq_some_iff.1 hA
  have hAm : A ∈ as := List.mem_of_find?_eq_some hfind
  obtain ⟨m, hm, hM⟩ := Meaning.message_of_layout F.layoutOk hl hAm
  have hA' : A ∈ as.filter fun a => a.message == A.message :=
    List.mem_filter.2 ⟨hAm, beq_self_eq_true _⟩
  obtain ⟨pad, hc, -, -, hrow, -⟩ := Meaning.block_of_message hM hA' hb
  have h0 : m.shape.mainRows ≠ 0 := by
    have := Nat.two_pow_pos b.rowBits
    omega
  have hsh := F.shapeAt born A.message o m ho hm
  obtain ⟨e1, e2⟩ := bits_main hsh h0
  rw [F.codes] at e2
  rw [e1, e2] at hJ hw
  rw [F.member o x y m.shape hsh hx hy, e1]
  obtain ⟨r1, r2⟩ := inBlock_inside hM hA' hb J hJ hw
  rw [Meaning.ell_pow F.lengths hc] at r2
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨r1, r2⟩

/-- **THE FIELD mask OF `InsideAt`.** -/
theorem insideAt_mask (a : K9.Part) (F : PartFits cs ms own a) :
    ∀ o j x y, K9L.maskOracle a.L.check.frame = some o →
      j < a.F.ns ∨ j < a.F.LS.size → K9.seatAt own a.d.book o = some x →
      (ms.find? fun y => decide (seatOf y = x)) = some y →
      InMsg cs (y.1.l.get y.2).1 true (j % 2 ^ a.d.st.rowBits o .mask)
        (j / 2 ^ a.d.st.rowBits o .mask) := by
  intro o j x y ho hj hx hy
  obtain ⟨sh, hsh, hR, hA, h1, h2⟩ := F.maskFits o ho
  rw [F.member o x y sh hsh hx hy, rowBits_mask hsh]
  exact (Meaning.mask_inside cs sh hR hA j (by rcases hj with h | h <;> omega)).1

/-- **`InsideAt` FROM `PartFits`.** -/
theorem insideAt_of_fits (a : K9.Part) (F : PartFits cs ms own a) : InsideAt cs ms own a :=
  ⟨insideAt_main cs ms own a F, insideAt_mask cs ms own a F⟩

end

/-- At one mask row. -/
theorem free_one {ell a : ℕ} (h : a ≤ ell) : Send.freeMaskEntries 1 ell a = ell - a := by
  unfold Send.freeMaskEntries
  have h' : ¬ ell < a := by omega
  simp [h']

/-- **The bound, from the written IOP's own public test.** -/
theorem room_of_linksLaid {links : Array Ok.Links.LinkD} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} (h : Ok.Links.linksLaid links codes shape layout = true) {l : ℕ}
    {X : Ok.Links.LinkD} (hX : links[l]? = some X) :
    X.ns ≤ Send.freeMaskEntries 1 (codes.mask.getD shape.maskCode default).ell shape.answers := by
  unfold Ok.Links.linksLaid at h
  cases hz : codes.mask[shape.maskCode]? with
  | none =>
    rw [hz] at h
    cases h
  | some zk =>
  rw [hz, Option.any_some] at h
  have e : codes.mask.getD shape.maskCode default = zk := by
    simp [Array.getD_eq_getD_getElem?, hz]
  have hm : (X, l) ∈ links.toList.zipIdx :=
    List.mem_zipIdx_iff_getElem?.2 (by simpa using hX)
  have h1 := List.all_eq_true.1 h (X, l) hm
  unfold Ok.Links.linkLaid at h1
  rw [Bool.and_eq_true, decide_eq_true_iff] at h1
  have h2 : X.ns + shape.answers ≤ zk.ell := h1.1
  rw [e, free_one (by omega)]
  omega

/-- **The clause maskFits, from the plan's test and four ties.** -/
theorem maskFits_of_plan (cs : OnBytes.Codes) (a : K9.Part) {links : Array Ok.Links.LinkD}
    {shape : Params.ReqShape} {layout : Params.ReqLayout}
    (h : Ok.Links.linksLaid links cs shape layout = true) {l : ℕ} {X : Ok.Links.LinkD}
    (hX : links[l]? = some X) (hA : 1 ≤ shape.answers)
    (hShape : ∀ o, K9L.maskOracle a.L.check.frame = some o →
      ∃ sh, (a.d.st.oracles[o]?).map (·.shape) = some sh ∧ sh.maskRows = 1 ∧
        sh.maskCode = shape.maskCode ∧ sh.answers = shape.answers)
    (hns : a.F.ns = X.ns) (hLS : a.F.LS.size ≤ a.F.ns) :
    ∀ o, K9L.maskOracle a.L.check.frame = some o →
      ∃ sh, (a.d.st.oracles[o]?).map (·.shape) = some sh ∧
        sh.maskRows = 2 ^ ceilLog2 sh.maskRows ∧ 1 ≤ sh.answers ∧
        a.F.ns ≤
          Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers ∧
        a.F.LS.size ≤
          Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers := by
  intro o ho
  obtain ⟨sh, h1, h2, h3, h4⟩ := hShape o ho
  have hr := room_of_linksLaid h hX
  refine ⟨sh, h1, by rw [h2]; rfl, by omega, ?_, ?_⟩ <;> rw [h2, h3, h4] <;> omega

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.insideAt_main
#print axioms VerifiableInference.Desc.Sound.insideAt_mask
#print axioms VerifiableInference.Desc.Sound.insideAt_of_fits
#print axioms VerifiableInference.Desc.Sound.room_of_linksLaid
#print axioms VerifiableInference.Desc.Sound.maskFits_of_plan
