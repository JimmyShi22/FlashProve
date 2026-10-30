-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/DebtsConst.lean: code switching (K2): THE SIX CLOSED PREMISES OF d_link |
d_head | d_finish (Johnson/P1K2R/DebtsAt.lean: hps · hnd · hbk · hok · hlenC · hcl), PAID AT THE
FIRST CHAIN's OWN SUB-PROTOCOLS, AND SO «the debts on the table's numbers» AT THE CLOSED CONSTANT's
OWN NUMBERS At.N Z c (P5J.At.N, Johnson/P5J/LettersAt.lean).
  hps_scope    hps: the sub-protocols' places are the written list (blockPlaces_full, SubsFull.lean)
  (hnd)        IM.places_nodup (Johnson/IMR/BorderW.lean), called
  block_at_no  hbk: below 358 there is a sub-protocol at each number
  hok_open    hok: the plan's shape of a request is lawful (ProofFile's startOk_shape at the first state)
  keptLen_full · keptLen_at  hlenC: BY LEAN's KERNEL at the 25 groups: the written table keeps as
               many seats of the segment in front as the written shape's target keeps members ·
               keptLen_can_fail: a negative test (moved by one)
  swBlock_link · swBlock_head · swBlock_fin  AT EACH OF THE 25 NUMBERS: the sub-protocol there tells
               oraclesAt n.grp n.codes n.sent, and its declared rounds draw n.positions positions:
               by the seats' own text (Johnson/IMR/: k2_link_sits | k2_head_of |
               k2_finish_of · K2Is.live), dress by dress. NO WRITTEN LIST OF ROUNDS IS WANTED
  swNo · find_by_place · find_full · findW_at  the search in possAt finds that sub-protocol: a rule
               on lists, and a closed fact on the written list of places, by the kernel ·
               find_can_fail: a negative test
  sent_written · sent_written_fin  the plan's n.sent IS the written list sentW g, at the written
               shape: on the plan alone (notices_sent, K2Hands/NoticesSent.lean)
  hcl_link · hcl_head · hcl_fin  hcl, whole
  d_link_all · d_head_all · d_finish_all  d_…_plain (HstPlain.lean) WITH THE SIX GONE, at numbers
               N₀.atBlocks Z.first.shape links c.blocksInOrder
  N_const · keptOf_const  the closed constant's At.N Z c is such numbers (P5J.At.N_atBlocks)
  d_link_const · d_head_const · d_finish_const  THE SAME AT At.N Z c
ON «THE HARD ONE» (possAt). The row's road went by the written list of declared rounds, cut by the
written cut's counts. It is not wanted: possAt reads the declared rounds of ONE sub-protocol, the
switch's own; what stands at that number is the kind's own sub-protocol at the plan's numbers, under
wrappers that leave its rounds: so its count of positions is n.positions by the texts.
WHAT STANDS IN FRONT OF THE TOPS, BY NAME. THE HEAD: hS · hR · O (at the public files' own layout
file) · hF · hpl. hy: madePinnedAt accepts · hcut · hB: sendsAreB accepts. hT: THE TEST sentFitB
ACCEPTS at the numbers, the group, the place, the public part's codes and the written list sentW g
(closed once the numbers are closed; not shown). hFk: what
the fence Fk holds is reached. In …_all: hkept: the numbers' keptOf is the written table's · hlk: 25
segments. In …_const: hkeptN: (At.N Z c).keptOf is the written table's: THE FIELD keptOf OF
AtWritten Z c (K2Ties/WrittenAt.lean: its at_written has it in scope, from LaidAt and hy; that file
is not imported here).
LIMITS. Joins, and two closed facts by the kernel. No premise is shown met at a real value: no
example. The full size alone. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.HstPlain
import Johnson.P1K2R.SitsDoor
import Johnson.Top.H0.Tw.K2C.PossAtK2
import Johnson.LPFK9R.SubsFull
import Johnson.IMR.BorderW
import Johnson.P5T.PlanSeatsFull
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces possAt possOf)
open VerifiableInference.Desc.First.K2 (SwState frontAt frameAt finishFrontQ LinkDebts SwitchDebts
  sentFitB)
open VerifiableInference.Desc.First.K2Hands (sentW shW)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (XK linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)
open ProofFile (Cl)

/-! ## Rules on lists, and closed facts -/

/-- The number of the switch into group g in the first chain's flat list. -/
def swNo (g : ℕ) : ℕ := if g ≤ 23 then 14 * g + 2 else if g = 24 then 339 else 353

theorem swNo_link {g : ℕ} (h : g ≤ 23) : swNo g = 14 * g + 2 := by
  unfold swNo
  rw [if_pos h]

theorem swNo_24 : swNo 24 = 339 := rfl

theorem swNo_25 : swNo 25 = 353 := rfl

/-- Where the places are a list without a twin, a search by the place finds the sub-protocol at the
number at which the search over the places ends. -/
theorem find_by_place {St Cl' : Type} {bs : List (Block St Cl')} {ps : List Place}
    (hps : blockPlaces bs = ps) (hnd : ps.Nodup) {k : ℕ} {b : Block St Cl'}
    (hbk : bs[k]? = some b) {p : Place → Bool} (hfind : ps.find? p = ps[k]?) :
    bs.find? (fun b => p b.place) = some b := by
  have hk : ps[k]? = some b.place := by
    rw [← hps]
    unfold blockPlaces
    rw [List.getElem?_map, hbk]
    rfl
  have e : (bs.find? (fun b => p b.place)).map (·.place) = some b.place := by
    have := List.find?_map (f := fun b : Block St Cl' => b.place) (p := p) (l := bs)
    rw [← hk, ← hfind, ← hps]
    unfold blockPlaces
    rw [this]
    rfl
  obtain ⟨b', hb', ep⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.mem_of_find?_eq_some hb')
  have hj' : ps[j]? = some b.place := by
    rw [← hps]
    unfold blockPlaces
    rw [List.getElem?_map, hj]
    exact congrArg some ep
  have hjl : j < ps.length := (List.getElem?_eq_some_iff.1 hj').1
  have ejk : j = k := (List.getElem?_inj hjl hnd (hj'.trans hk.symm))
  subst ejk
  rw [hb']
  exact hj.symm.trans hbk

set_option maxRecDepth 1000000 in
/-- **By the kernel**: in the written list of places the first of the kind K2 at segment g (the
finish: 25) has the number swNo g. -/
theorem find_full : (List.range 25).all (fun i => decide
    (placesW.find? (fun q => q.kind == .K2 && q.link.getD 25 == i + 1) = placesW[swNo (i + 1)]?)) =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the search at segment 1 does not end at the number of the switch into group 2.
-/
theorem find_can_fail : decide
    (placesW.find? (fun q => q.kind == .K2 && q.link.getD 25 == 1) = placesW[swNo 2]?) = false := by
  decide +kernel

theorem findW_at {g : ℕ} (h1 : 1 ≤ g) (h25 : g ≤ 25) :
    placesW.find? (fun q => q.kind == .K2 && q.link.getD 25 == g) = placesW[swNo g]? := by
  have k := of_decide_eq_true (List.all_eq_true.1 find_full (g - 1) (List.mem_range.2 (by omega)))
  rwa [show g - 1 + 1 = g by omega] at k

set_option maxRecDepth 1000000 in
/-- **By the kernel**: hlenC at the written table and the written shape, at the 25 groups. -/
theorem keptLen_full : (List.range 25).all (fun i =>
    (P5T.N0Full.keptOf i).length == ((reqGroups shW).getD (i + 1) {}).target.kept.size) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the table's segments moved by one against the shape's groups. -/
theorem keptLen_can_fail : (List.range 24).all (fun i =>
    (P5T.N0Full.keptOf i).length == ((reqGroups shW).getD (i + 2) {}).target.kept.size) =
    false := by
  decide +kernel

theorem keptLen_at {N₀ : Numbers} {sh : Params.ReqShape} (hk : N₀.keptOf = P5T.N0Full.keptOf)
    (hsh : sh = shW) {i : ℕ} (hi : i < 25) :
    (N₀.keptOf (i + 1 - 1)).length = ((reqGroups sh).getD (i + 1) {}).target.kept.size := by
  have k := List.all_eq_true.1 keptLen_full i (List.mem_range.2 hi)
  rw [hk, hsh, Nat.add_sub_cancel]
  exact beq_iff_eq.1 k

/-! ## The plan's n.sent is the written list -/

/-- **At a link or at the output head.** -/
theorem sent_written {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : Prep} {l : ℕ} {n : Nums}
    (hP : prepOf Z G = some Pp) (hn : numsAt Pp (some l) = some n) (hsh : G.first.shape = shW)
    (h25 : l < 25) : n.sent.toList = sentW l := by
  obtain ⟨e1, -, e3⟩ := Meaning.Carry.prep_facts hP
  obtain ⟨h0, f', lay, hf', -, es, -, -⟩ := Meaning.Carry.nums_facts hn
  have hlen : Pp.z.request.link.length = 25 := by rw [e1, hsh]; exact shW_links
  have hsz : l < (reqGroups Pp.z.request).size := by
    rw [Meaning.Carry.reqGroups_size, hlen]; omega
  have hG : (reqGroups Pp.z.request)[l]? = some ((reqGroups Pp.z.request).getD l {}) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
    rfl
  obtain ⟨nF, hF, eN⟩ := VerifiableInference.Desc.First.K2Hands.notices_sent Pp.z
    (Verify.subproofsWith G.W G.first.shape.link)
    (VerifiableInference.Desc.First.K2.frameAtLink Pp.z.request l) rfl rfl
    (Nat.pos_of_ne_zero h0) (by show l ≤ _; omega) _ hG
  rw [← e3] at hF
  obtain rfl : f' = nF := Option.some.inj (hf'.symm.trans hF)
  rw [es, List.toList_toArray, ← eN, e1, hsh]
  unfold sentW
  rw [if_neg (by omega)]
  rfl

/-- **At the finish.** -/
theorem sent_written_fin {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : Prep} {n : Nums}
    (hP : prepOf Z G = some Pp) (hn : numsAt Pp none = some n) (hsh : G.first.shape = shW) :
    n.sent.toList = sentW 25 := by
  obtain ⟨e1, -, e3⟩ := Meaning.Carry.prep_facts hP
  obtain ⟨h0, f', lay, hf', -, es, -⟩ := Meaning.Carry.nums_facts_none hn
  have hlen : Pp.z.request.link.length = 25 := by rw [e1, hsh]; exact shW_links
  rw [hlen] at hf'
  have hsz : 25 < (reqGroups Pp.z.request).size := by
    rw [Meaning.Carry.reqGroups_size, hlen]; omega
  have hG : (reqGroups Pp.z.request)[25]? = some ((reqGroups Pp.z.request).getD 25 {}) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz]
    rfl
  obtain ⟨nF, hF, eN⟩ := VerifiableInference.Desc.First.K2Hands.notices_sent Pp.z
    (Verify.subproofsWith G.W G.first.shape.link)
    (VerifiableInference.Desc.First.K2.frameAtLink Pp.z.request 25) rfl rfl
    (by show 0 < 25; omega) (by show 25 ≤ _; omega) _ hG
  rw [← e3] at hF
  obtain rfl : f' = nF := Option.some.inj (hf'.symm.trans hF)
  rw [Meaning.Carry.atMoment_end (by show 25 = _; exact hlen.symm)] at eN
  rw [es, List.toList_toArray, ← eN, e1, hsh]
  unfold sentW
  rw [if_pos rfl]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-! ## hps · hbk · hok -/

theorem hps_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    blockPlaces c.blocksInOrder = placesW := by
  rw [LPFK9.blockPlaces_full hS hR O, ← LPFK9.linksW_full]
  rfl

theorem block_at_no (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : k < 358) :
    ∃ b, c.blocksInOrder[k]? = some b :=
  ⟨_, List.getElem?_eq_getElem (by rw [Meaning.K2.flat_358 hS O]; exact hk)⟩

theorem hok_open (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    reqShapeOk Z.first.shape = true :=
  ProofFile.Law.startOk_shape (ProofFile.Law.startP_ok (Meaning.K2.pub_start O.pub))

/-! ## What stands at a switch's number -/

/-- **At a link's switch, 1 ≤ l < 24.** -/
theorem swBlock_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ b, c.blocksInOrder[14 * l + 2]? = some b ∧ ∀ Pp n, prepOf Z Bs.G₀ = some Pp →
      numsAt Pp (some l) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧ possOf b = n.positions := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb := flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hb)).1
  refine ⟨b, hf, fun Pp n hP hn => ?_⟩
  obtain ⟨P', n', hP', hn', hd⟩ := hi.live hxp
  obtain rfl : P' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  obtain ⟨fs, f, -, -, eb⟩ := hl
  rcases hd with ⟨ha, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
  · cases ha
  · rw [eb, ex]
    refine ⟨?_, VerifiableInference.Desc.First.K2.possOf_k2 (Cl := Unit) (k2P Z _ x.name .head n')⟩
    show List.flatten [oraclesAt n'.grp n'.codes n'.sent, []] = _
    simp
  · rw [eb, ex]
    refine ⟨?_, VerifiableInference.Desc.First.K2.possOf_k2 (Cl := Unit) (k2P Z _ x.name .link n')⟩
    show List.flatten [oraclesAt n'.grp n'.codes n'.sent, []] = _
    simp

/-- **At the output head's switch.** -/
theorem swBlock_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ b, c.blocksInOrder[339]? = some b ∧ ∀ Pp n, prepOf Z Bs.G₀ = some Pp →
      numsAt Pp (some 24) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧ possOf b = n.positions := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
  have hb := flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  refine ⟨b, hf, fun Pp n hP hn => ?_⟩
  obtain ⟨P', n', hP', hn', hd⟩ := hi.live hxp
  obtain rfl : P' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  have eb : b = IM.seatedAs ProofFile.sameReply x.retype b.name _ := hl
  rcases hd with ⟨ha, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
  · cases ha
  · rw [eb, ex]
    refine ⟨?_, VerifiableInference.Desc.First.K2.possOf_k2 (Cl := Unit) (k2P Z _ x.name .head n')⟩
    show List.flatten [oraclesAt n'.grp n'.codes n'.sent, []] = _
    simp
  · rw [eb, ex]
    refine ⟨?_, VerifiableInference.Desc.First.K2.possOf_k2 (Cl := Unit) (k2P Z _ x.name .link n')⟩
    show List.flatten [oraclesAt n'.grp n'.codes n'.sent, []] = _
    simp

/-- **At the finish's switch.** -/
theorem swBlock_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ b, c.blocksInOrder[353]? = some b ∧ ∀ Pp n, prepOf Z Bs.G₀ = some Pp →
      numsAt Pp none = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧ possOf b = n.positions := by
  obtain ⟨b, x, e1, hx, ep, hl, -⟩ := IM.k2_finish_of O
  have hi := IM.k2_mem hx
  rw [ep] at hi
  have hix := (IM.back_numbers hS hR O).1 0 b e1
  have hb := back_planOk O hpl (List.mem_of_getElem? e1)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  refine ⟨_, hix, fun Pp n hP hn => ?_⟩
  obtain ⟨P', n', hP', hn', hd⟩ := hi.live hxp
  obtain rfl : P' = Pp := Option.some.inj (hP'.symm.trans hP)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  have eb : b = IM.seatedAs ProofFile.sameReply x.retype b.name _ := hl
  rcases hd with ⟨-, ex⟩ | ⟨l', HP, ha, -⟩ | ⟨l', ha, -⟩
  · rw [eb, ex]
    refine ⟨?_,
      VerifiableInference.Desc.First.K2.possOf_k2 (Cl := Unit) (k2P Z _ x.name .finish n')⟩
    show List.flatten [oraclesAt n'.grp n'.codes n'.sent, []] = _
    simp
  · cases ha
  · cases ha

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {N₀ : Numbers} {links : List ModelPart}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

/-! ## hcl, whole -/

theorem hcl_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hlk : links.length = 25)
    {m : ℕ} (h23 : m < 23)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) (m + 1) placesW[14 * (m + 1) + 2]?
      Z.first.codes (sentW (m + 1)).toArray = true) {b : Block S Cl}
    (hbk : c.blocksInOrder[14 * (m + 1) + 2]? = some b) :
    ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) (m + 1) placesW[14 * (m + 1) + 2]? n.codes
        n.sent = true ∧
      possAt c.blocksInOrder links.length (m + 1) = n.positions := by
  intro Pp n hP hn
  obtain ⟨b', hb', H⟩ := swBlock_link hS hR O hpl (l := m + 1) (by omega) (by omega)
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hbk)
  obtain ⟨c1, c3⟩ := H Pp n hP hn
  have hsh : Bs.G₀.first.shape = shW := by rw [O.first]; exact (written3 hS O.pub hy).2.1
  have es : n.sent = (sentW (m + 1)).toArray := by rw [← sent_written hP hn hsh (by omega)]
  refine ⟨c1, by rw [codes_at O hP hn, es]; exact hT, ?_⟩
  rw [hlk, ← c3]
  exact VerifiableInference.Desc.First.K2.possAt_found
    (find_by_place (hps_scope hS hR O) IM.places_nodup hbk
      ((findW_at (g := m + 1) (by omega) (by omega)).trans (by rw [swNo_link (by omega)])))

theorem hcl_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hlk : links.length = 25)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 24 placesW[339]?
      Z.first.codes (sentW 24).toArray = true) {b : Block S Cl}
    (hbk : c.blocksInOrder[339]? = some b) :
    ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 24 placesW[339]? n.codes
        n.sent = true ∧
      possAt c.blocksInOrder links.length 24 = n.positions := by
  intro Pp n hP hn
  obtain ⟨b', hb', H⟩ := swBlock_head hS hR O hpl
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hbk)
  obtain ⟨c1, c3⟩ := H Pp n hP hn
  have hsh : Bs.G₀.first.shape = shW := by rw [O.first]; exact (written3 hS O.pub hy).2.1
  have es : n.sent = (sentW 24).toArray := by rw [← sent_written hP hn hsh (by omega)]
  refine ⟨c1, by rw [codes_at O hP hn, es]; exact hT, ?_⟩
  rw [hlk, ← c3]
  exact VerifiableInference.Desc.First.K2.possAt_found
    (find_by_place (hps_scope hS hR O) IM.places_nodup hbk
      ((findW_at (g := 24) (by omega) (by omega)).trans (by rw [swNo_24])))

theorem hcl_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hlk : links.length = 25)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 25 placesW[353]?
      Z.first.codes (sentW 25).toArray = true) {b : Block S Cl}
    (hbk : c.blocksInOrder[353]? = some b) :
    ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 25 placesW[353]? n.codes
        n.sent = true ∧
      possAt c.blocksInOrder links.length 25 = n.positions := by
  intro Pp n hP hn
  obtain ⟨b', hb', H⟩ := swBlock_fin hS hR O hpl
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hbk)
  obtain ⟨c1, c3⟩ := H Pp n hP hn
  have hsh : Bs.G₀.first.shape = shW := by rw [O.first]; exact (written3 hS O.pub hy).2.1
  have es : n.sent = (sentW 25).toArray := by rw [← sent_written_fin hP hn hsh]
  refine ⟨c1, by rw [codes_at O hP hn, es]; exact hT, ?_⟩
  rw [hlk, ← c3]
  exact VerifiableInference.Desc.First.K2.possAt_found
    (find_by_place (hps_scope hS hR O) IM.places_nodup hbk
      ((findW_at (g := 25) (by omega) (by omega)).trans (by rw [swNo_25])))

/-! ## The spender's three with the six gone -/

theorem d_link_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkept : N₀.keptOf = P5T.N0Full.keptOf) (hlk : links.length = 25)
    {m : ℕ} (h23 : m < 23)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) (m + 1) placesW[14 * (m + 1) + 2]?
      Z.first.codes (sentW (m + 1)).toArray = true)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
        ∀ Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      Fk (14 * (m + 1) + 2) s →
      XK (N₀.atBlocks Z.first.shape links c.blocksInOrder) linksW placesW E (14 * (m + 1) + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      LinkDebts (N₀.atBlocks Z.first.shape links c.blocksInOrder) (m + 1) placesW[14 * (m + 1) + 2]?
        placesW[14 * (m + 1) + 3]? s n.positions x W lay' := by
  obtain ⟨b, hbk⟩ := block_at_no hS O (k := 14 * (m + 1) + 2) (by omega)
  exact d_link_plain hS hR O hF hpl hy hcut hB h23 hFk (hps_scope hS hR O) IM.places_nodup hbk
    (hok_open O) (keptLen_at hkept (written3 hS O.pub hy).2.1 (i := m) (by omega))
    (hcl_link hS hR O hpl hy hlk h23 hT hbk)

theorem d_head_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkept : N₀.keptOf = P5T.N0Full.keptOf) (hlk : links.length = 25)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 24 placesW[339]?
      Z.first.codes (sentW 24).toArray = true)
    (hFk : ∀ s, Fk (339) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (339) (z, s)) :
        ∀ nm Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks Z.first.shape links c.blocksInOrder) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links c.blocksInOrder) 24 placesW[339]? placesW[339 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size + x.own.length) x W lay' := by
  obtain ⟨b, hbk⟩ := block_at_no hS O (k := 339) (by omega)
  exact d_head_plain hS hR O hF hpl hy hcut hB hFk (hps_scope hS hR O) IM.places_nodup hbk
    (hok_open O) (keptLen_at hkept (written3 hS O.pub hy).2.1 (i := 23) (by omega))
    (hcl_head hS hR O hpl hy hlk hT hbk)

theorem d_finish_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkept : N₀.keptOf = P5T.N0Full.keptOf) (hlk : links.length = 25)
    (hT : sentFitB (N₀.atBlocks Z.first.shape links c.blocksInOrder) 25 placesW[353]?
      Z.first.codes (sentW 25).toArray = true)
    (hFk : ∀ s, Fk (353) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (353) (z, s)) :
        ∀ nm Pp n (s t : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      Fk 353 s → XK (N₀.atBlocks Z.first.shape links c.blocksInOrder) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links c.blocksInOrder) 25 placesW[353]? placesW[353 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size) x W lay' := by
  obtain ⟨b, hbk⟩ := block_at_no hS O (k := 353) (by omega)
  exact d_finish_plain hS hR O hF hpl hy hcut hB hFk (hps_scope hS hR O) IM.places_nodup hbk
    (hok_open O) (keptLen_at hkept (written3 hS O.pub hy).2.1 (i := 24) (by omega))
    (hcl_fin hS hR O hpl hy hlk hT hbk)

/-! ## At the closed constant's own numbers -/

/-- The closed constant's At.N Z c is «the numbers closed over the sub-protocols». -/
theorem N_const (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    P5J.At.N Z c = (P5T.numbersOf (P5J.At.pseats Z)).atBlocks Z.first.shape P5J.At.links c.blocksInOrder :=
  P5J.At.N_atBlocks Z c (LPFK9.blockPlaces_full hS hR O)

theorem keptOf_const (hkeptN : (P5J.At.N Z c).keptOf = P5T.N0Full.keptOf)
    (eN : P5J.At.N Z c =
      (P5T.numbersOf (P5J.At.pseats Z)).atBlocks Z.first.shape P5J.At.links c.blocksInOrder) :
    (P5T.numbersOf (P5J.At.pseats Z)).keptOf = P5T.N0Full.keptOf := by
  rw [eN] at hkeptN
  exact hkeptN

theorem d_link_const (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkeptN : (P5J.At.N Z c).keptOf = P5T.N0Full.keptOf)
    {m : ℕ} (h23 : m < 23)
    (hT : sentFitB (P5J.At.N Z c) (m + 1) placesW[14 * (m + 1) + 2]?
      Z.first.codes (sentW (m + 1)).toArray = true)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
        ∀ Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      Fk (14 * (m + 1) + 2) s →
      XK (P5J.At.N Z c) linksW placesW E (14 * (m + 1) + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      LinkDebts (P5J.At.N Z c) (m + 1) placesW[14 * (m + 1) + 2]?
        placesW[14 * (m + 1) + 3]? s n.positions x W lay' := by
  have eN := N_const hS hR O
  rw [eN] at hT ⊢
  exact d_link_all hS hR O hF hpl hy hcut hB (keptOf_const hkeptN eN) rfl h23 hT hFk

theorem d_head_const (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkeptN : (P5J.At.N Z c).keptOf = P5T.N0Full.keptOf)
    (hT : sentFitB (P5J.At.N Z c) 24 placesW[339]?
      Z.first.codes (sentW 24).toArray = true)
    (hFk : ∀ s, Fk (339) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (339) (z, s)) :
        ∀ nm Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      Fk 339 s → XK (P5J.At.N Z c) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (P5J.At.N Z c) 24 placesW[339]? placesW[339 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size + x.own.length) x W lay' := by
  have eN := N_const hS hR O
  rw [eN] at hT ⊢
  exact d_head_all hS hR O hF hpl hy hcut hB (keptOf_const hkeptN eN) rfl hT hFk

theorem d_finish_const (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hkeptN : (P5J.At.N Z c).keptOf = P5T.N0Full.keptOf)
    (hT : sentFitB (P5J.At.N Z c) 25 placesW[353]?
      Z.first.codes (sentW 25).toArray = true)
    (hFk : ∀ s, Fk (353) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (353) (z, s)) :
        ∀ nm Pp n (s t : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      Fk 353 s → XK (P5J.At.N Z c) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (P5J.At.N Z c) 25 placesW[353]? placesW[353 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size) x W lay' := by
  have eN := N_const hS hR O
  rw [eN] at hT ⊢
  exact d_finish_all hS hR O hF hpl hy hcut hB (keptOf_const hkeptN eN) rfl hT hFk

end

end P1K2

#print axioms P1K2.swNo_link
#print axioms P1K2.find_by_place
#print axioms P1K2.find_full
#print axioms P1K2.find_can_fail
#print axioms P1K2.findW_at
#print axioms P1K2.keptLen_full
#print axioms P1K2.keptLen_can_fail
#print axioms P1K2.keptLen_at
#print axioms P1K2.sent_written
#print axioms P1K2.sent_written_fin
#print axioms P1K2.hps_scope
#print axioms P1K2.block_at_no
#print axioms P1K2.hok_open
#print axioms P1K2.swBlock_link
#print axioms P1K2.swBlock_head
#print axioms P1K2.swBlock_fin
#print axioms P1K2.hcl_link
#print axioms P1K2.hcl_head
#print axioms P1K2.hcl_fin
#print axioms P1K2.d_link_all
#print axioms P1K2.d_head_all
#print axioms P1K2.d_finish_all
#print axioms P1K2.N_const
#print axioms P1K2.keptOf_const
#print axioms P1K2.d_link_const
#print axioms P1K2.d_head_const
#print axioms P1K2.d_finish_const
