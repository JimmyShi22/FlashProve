--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SitsSwitch.lean: BESIDE Johnson/Desc/K1/Law/Sits.lean: FOR THE ROW
«K01_port_at_switches» (no part of K01_sits, which speaks of the places of the kind K1): THE
TWENTY-FIVE PLACES OF A PROOF FILE's FIRST CHAIN AT WHICH THE CODE SWITCH (kind K2) HANDS ITS
SENDING TO K1's TEXT: the written sendings number 3 l, l from 1 to 25. THE SEAT AND THE NUMBERS. A
JOIN OF THREE HOUSES' THEOREMS AND ONE CLOSED TEST.
  (b) THE SEAT (IM.k2_link_sits | k2_head_of | k2_finish_of): the entry
      of the description's own chain there is a member x of K2's lot's table under the seat's
      wrappers, K2Is at its address; where x passes its test on the plan it is K2's own constant
      codeSwitchKind (k2P Z a nm st n) in one of three dresses (part 1's P1K2.Dressed), n := the lot's own
      numbers: prepOf Z G₀ = some Pp and numsAt Pp a.link = some n.
  (n) THE NUMBERS. Opens.lean leaves open «that the switching kind's place announces openSent»
      its house's equation». Here it is paid AT THE LOT's OWN NUMBERS n: where the
      test madeRow accepts, prepOf Z G₀ is the written value IM.prepW (prep_pinned), so n
      is a closed value; switches_written: at each l from 1 to 25 the numbers
      that numsAt gives there have the written codes, and what they announce is openSent shapeFull
      l: ONE evaluation in Lean's kernel. So the parameters parSwitchK2 a ft n, made of n's codes,
      samples, bits of work and messages, stand on the written sending 3 l (PlaceOk 2 0 (3 l)).
  parSwitchK2 · parSwitchK2_sent · linkOfGroup
  switchesTest · switches_written   the test and its yes
  prepW_some · switch_shifted_no · switch_none_at_0 · switch_none_at_26   it is no fall-back; a
      negative test: THE TEST ITSELF at shift 1 (each group's numbers against the next group's
      messages) says no; two facts on numsAt: no numbers at link 0; none at link 26.
  nums_written · placeOk_switch     what the test gives, at one l
  SwitchAt Z G a nm x k             the numbers n · the dress at that very n · PlaceOk 2 0 k
  switchAt_of                       from Dressed, under the pin
  k01_switch_seat_link (1 ≤ l < 24) · k01_switch_seat_head (l = 24) · k01_switch_seat_finish
      (l = 25)

THE PREMISES, BY NAME: hS hR O: as in Sits.lean · hy: madeRow Z = true: a test
with code on the public files (the door's second list asks it) · inside each statement: x.planOk =
true: the lot's member passes its test on the plan (else it is a mute that always refuses).
What is not claimed. THAT A YES OF THE SWITCH HOLDS A YES OF K1's DECISION AT parSwitchK2 a ft n:
the switch's decision takes what it announces off the verifier's state, not off n (part 1's
Johnson/Top/H0/Tw/K2C/SendsOpen.lean says so): that wants part 1's fence at the state in front, and
is not here. That the premises can be met together: no member is shown. The five switches of the
last group's test; the later chains; the key file; the small size. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.K1.Law.Sits
import Johnson.P1K2R.Sits
import Johnson.IMR.SendsPinned

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (codeSwitchKind finishPlace headOpened)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (madeRow)
open ProofFile (Cl)
open IM (Open LaidAlone Joined K2Is k2P under)

/-- **The parameters that a code switch hands to K1's text**, made of the lot's own numbers. ft: the
number of the chain's first tree. -/
def parSwitchK2 (a : Place) (ft : Nat) (n : P1K2.Nums) : Par :=
  { place := a, codes := n.codes, gp := ⟨n.samples, ft⟩, work := n.work₁,
    parts := [("the switch's sending", n.sent)] }

theorem parSwitchK2_sent (a : Place) (ft : Nat) (n : P1K2.Nums) :
    (parSwitchK2 a ft n).sent = n.sent := by
  simp [Par.sent, parSwitchK2]

/-- The link of the place at which the switch into group l stands: behind the links at l = 25. -/
def linkOfGroup (l : Nat) : Option Nat := if l = 25 then none else some l

/-- **The test**: at the written numbers, group by group. shift: 0 is the test; another number holds
group l's numbers against group l + shift's messages: for a negative test. -/
def switchesTest (shift : Nat) : Bool :=
  IM.prepW.any fun Pp => (List.range 25).all fun i =>
    (P1K2.numsAt Pp (linkOfGroup (i + 1))).any fun n =>
      decide (n.codes = codesFull2) && decide (n.sent.toList = openSent shapeFull (i + 1 + shift))

theorem switches_written : switchesTest 0 = true := by decide +kernel

/-- The written value is no fall-back. -/
theorem prepW_some : IM.prepW.isSome = true := by decide +kernel

/-- A negative test: THE TEST ITSELF, each group's numbers held against the next group's messages,
says no: at one group at the least they differ. -/
theorem switch_shifted_no : switchesTest 1 = false := by decide +kernel

/-- A negative test: there are no numbers at link 0. -/
theorem switch_none_at_0 : (IM.prepW.any fun Pp => (P1K2.numsAt Pp (some 0)).isSome) = false := by
  decide +kernel

/-- A negative test: there are none at link 26. -/
theorem switch_none_at_26 : (IM.prepW.any fun Pp => (P1K2.numsAt Pp (some 26)).isSome) = false := by
  decide +kernel

/-- What the test gives at one group. -/
theorem nums_written {Pp : P1K2.Prep} (hP : IM.prepW = some Pp) {l : Nat} (h1 : 1 ≤ l) (h2 : l ≤ 25)
    {n : P1K2.Nums} (hn : P1K2.numsAt Pp (linkOfGroup l) = some n) :
    n.codes = codesFull2 ∧ n.sent.toList = openSent shapeFull l := by
  obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
  have h := switches_written
  unfold switchesTest at h
  rw [hP] at h
  simp only [Option.any_some, List.all_eq_true, List.mem_range] at h
  have hi := h i (by omega)
  rw [hn] at hi
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi

/-- **The numbers' half**: the lot's own numbers stand on the written sending 3 l. -/
theorem placeOk_switch {Pp : P1K2.Prep} (hP : IM.prepW = some Pp) {l : Nat} (h1 : 1 ≤ l)
    (h2 : l ≤ 25) {n : P1K2.Nums} (hn : P1K2.numsAt Pp (linkOfGroup l) = some n) (a : Place)
    (ft : Nat) : PlaceOk 2 0 (3 * l) (parSwitchK2 a ft n) := by
  obtain ⟨hc, hs⟩ := nums_written hP h1 h2 hn
  exact k01_open opens_full _ l hc (by rw [parSwitchK2_sent]; exact hs) h1
    (by rw [full_links]; exact h2)

/-- **What is had at a switch's place**: the lot's numbers, the dress at these very numbers, and the
written sending number k. -/
def SwitchAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (x : Block S Unit)
    (k : Nat) : Prop :=
  ∃ Pp n, P1K2.prepOf Z G = some Pp ∧ P1K2.numsAt Pp a.link = some n ∧
    ((a.link = none ∧ x = under nm a (finishPlace (k2P Z a nm .finish n))) ∨
      (∃ l HP, a.link = some l ∧ P1K2.pureLetters G l = some HP ∧
        x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm (headOpened nm a HP))) ∨
      (∃ l, a.link = some l ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n)))) ∧
    PlaceOk 2 0 k (parSwitchK2 a Z.P.firstTree n)

theorem switchAt_of {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hy : madeRow Z = true)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) {a : Place} {nm : String} {x : Block S Unit}
    (hD : P1K2.Dressed Z G a nm x) {l : Nat} (h1 : 1 ≤ l) (h2 : l ≤ 25)
    (ha : a.link = linkOfGroup l) : SwitchAt Z G a nm x (3 * l) := by
  obtain ⟨Pp, n, hP, hn, hd⟩ := hD
  exact ⟨Pp, n, hP, hn, hd,
    placeOk_switch ((IM.prep_pinned h hy hG).symm.trans hP) h1 h2 (ha ▸ hn) a _⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The seat and the numbers at the switch into group l, at the links 1 to 23.** -/
theorem k01_switch_seat_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hy : madeRow Z = true) :
    ∀ l, 1 ≤ l → l < 24 → ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
      c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧
      Joined Z l b x.retype { chain := 1, link := some l, piece := 1, kind := .K2 } ∧
      K2Is Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x ∧
      (x.planOk = true →
        SwitchAt Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x
          (3 * l)) := by
  intro l h1 h24
  obtain ⟨Lk, b, x, e1, e2, -, hl, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  refine ⟨Lk, b, x, e1, e2, hl, hi, fun hp => ?_⟩
  refine switchAt_of O.pub hy O.blank (P1K2.is_planOk hi hp) h1 (by omega) ?_
  show some l = linkOfGroup l
  unfold linkOfGroup
  rw [if_neg (by omega)]

/-- **At the head's link: the switch into group 24.** -/
theorem k01_switch_seat_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hy : madeRow Z = true) :
    ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Block S Unit),
      c.links[24]? = some Lk ∧ Lk.hear[1]? = some b ∧
      LaidAlone ProofFile.sameReply b x.retype b.name
        { chain := 1, link := some 24, piece := 2, kind := .K2 } ∧
      K2Is Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x ∧
      (x.planOk = true →
        SwitchAt Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x 72) := by
  obtain ⟨Lk, b, x, e1, e2, -, hl, hi⟩ := IM.k2_head_of hS hR O
  exact ⟨Lk, b, x, e1, e2, hl, hi, fun hp =>
    switchAt_of (l := 24) O.pub hy O.blank (P1K2.is_planOk hi hp) (by omega) (by omega) rfl⟩

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Behind the links: the switch into the last group, number 25.** At every o. -/
theorem k01_switch_seat_finish (O : Open o pol lay KL F Z Bs base c A B) (hy : madeRow Z = true) :
    ∃ (b : Block S Cl) (x : Block S Unit), c.back[0]? = some b ∧
      LaidAlone ProofFile.sameReply b x.retype b.name IM.k2PlaceF ∧
      K2Is Z Bs.G₀ IM.k2PlaceF x.name x ∧
      (x.planOk = true → SwitchAt Z Bs.G₀ IM.k2PlaceF x.name x 75) := by
  obtain ⟨b, x, e1, hx, ep, hl, -⟩ := IM.k2_finish_of O
  have hi := IM.k2_mem hx
  rw [ep] at hi
  exact ⟨b, x, e1, hl, hi, fun hp =>
    switchAt_of (l := 25) O.pub hy O.blank (P1K2.is_planOk hi hp) (by omega) (by omega) rfl⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.parSwitchK2_sent
#print axioms VerifiableInference.Desc.K1.switches_written
#print axioms VerifiableInference.Desc.K1.prepW_some
#print axioms VerifiableInference.Desc.K1.switch_shifted_no
#print axioms VerifiableInference.Desc.K1.switch_none_at_0
#print axioms VerifiableInference.Desc.K1.switch_none_at_26
#print axioms VerifiableInference.Desc.K1.nums_written
#print axioms VerifiableInference.Desc.K1.placeOk_switch
#print axioms VerifiableInference.Desc.K1.switchAt_of
#print axioms VerifiableInference.Desc.K1.k01_switch_seat_link
#print axioms VerifiableInference.Desc.K1.k01_switch_seat_head
#print axioms VerifiableInference.Desc.K1.k01_switch_seat_finish
