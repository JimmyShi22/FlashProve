-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SendsPinned.lean: THE TEST sendsAreB AT THE TABLE snAt, WHERE THE TEST madeRow
(Johnson/Desc/Ok/PlanWritten/MadeTest.lean) ACCEPTS: 77 of the 78 numbers that send are paid
outright; the 78th (number 354: K12's five sendings) is left as ONE equation.

WHY. K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true is a premise that stands in front of the five facts at the first chain's last state (Johnson/IMR/EndFivePaid.lean: hB) and of seatsCarried (Johnson/IMR/SendsFinal.lean: hB). It says: the planning program's list of the first chain's sendings, sorted by entry, is what the 358 places send, in order. It had been evaluated (it accepts at the release's public files) and proved at no list.

HOW. (1) sentAtPlace reads of Z and G four things alone: G.first.shape · G.first.lin · P1K2.prepOf Z G · K12's five sendings: sent_by, BY rfl AT EVERY KIND OF PLACE: so firstOn | laterOn | wOn | sentBy below are the library's own functions in other letters, not a second text. (K1's parameter gp is not read by what is sent.) (2) P1K2.prepareAt reads the public X not at all: Plan.framesOf takes of subproofsWith X … only openRows, a list of ones: prepareAt_on. (3) Where madeRow Z = true, the sized proof, the first chain's shape, lin and codes and the planner's three lists are the written ones (sameProof_eq, Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean · proofSends_of_is, SendsTestLaws.lean beside it; firstIs's own equations): pins. The guard «tied» of prepareAt follows from these and from s₀'s own making (pub_start; S.startOk asks shape.answers == P.samples): prep_pinned. (4) The written list's entries already rise (sorted_written, by the kernel): so the sort is idle (core's mergeSort_of_pairwise; List.mergeSort itself does not reduce in the kernel). (5) ONE CLOSED EQUATION BY THE KERNEL: closed_but_354: the written 82 sendings are the 76 of numbers 0 to 353, then the written list's 77th to 81st, then the one of numbers 355 to 357.

WHAT IS SAID.
  sent_by · prepareAt_on        the two ties to the library's functions
  pins · prep_pinned · sn_pinned · left_pinned   what madeRow pins
  closed_but_354                the closed equation · closed_can_fail: a weak control (see its note)
  sends_but_354                 SendsAre … with the written five laid at 354: NO PREMISE ON K12
  sends_pinned                  sendsAreB … = true, under h354 : K12's five sendings are the written five

THE PREMISES. O : IM.Open …, at every o: free, by seat_open, wherever onlineDescription returns · hy : PlanWritten.madeRow Z = true (Johnson/Desc/Ok/PlanWritten/MadeTest.lean): not shown here · h354: OWED: four laws are said to pin it (place_L_of_full · idx_L_of_full · idx_of_planOk | nums_of_planOk · atFull_of_pubPlain): not called here. THE GOALS' SCOPE IS NOT ASKED.

What is not claimed. hy and h354 are shown nowhere here. No soundness.

-/
import Johnson.Desc.K12.Door.SentAtPlace
import Johnson.Desc.Ok.PlanWritten.MadeTest
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws
import Johnson.IMR.WrittenList
import Johnson.IMR.SeatOpen
import Johnson.IMR.RecRun
import Johnson.IMR.ArraysOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (sentAtPlace snAt SendsAre sendsAreB)
open VerifiableInference.PlanWritten (proofSizedFull madeRow madeIs firstIs sameProof_eq proofSends_of_is)
open ProofFile (Cl)

/-- K1's first sending, read off the shape alone. -/
def firstOn (sh : ReqShape) : Array OracleNotice :=
  let f₀ : ReqFrame := { shape := sh, groups := reqGroups sh }
  (([ReqFrame.notices (f₀.atMoment 0), #[foldMaskNotice (f₀.foldShape 0 {})], sh.atStart.toArray] :
    List (Array OracleNotice)).flatMap (·.toList)).toArray

/-- K1's later sendings, read off the shape alone. -/
def laterOn (sh : ReqShape) (link moment : Nat) : Array OracleNotice :=
  let f : ReqFrame := { shape := sh, groups := reqGroups sh, link := link }
  (([ReqFrame.notices (f.atMoment moment)] : List (Array OracleNotice)).flatMap (·.toList)).toArray

/-- W's sending. -/
def wOn (msg : Array OracleNotice) : Array OracleNotice :=
  (([msg] : List (Array OracleNotice)).flatMap (·.toList)).toArray

/-- K2's numbers' ground, read off the sized proof and the number of links alone. -/
def prepOn (z : ProofSized) (n : Nat) : Option P1K2.Prep := do
  let trees ← (List.range z.request.link.length).mapM
    (P1K2.treesOfLink z.codes { shape := z.request, groups := reqGroups z.request })
  pure ⟨z, Plan.framesFrom z 0 (reqGroups z.request).toList z.request.link (List.replicate n 1)
    z.link.group, trees⟩

/-- What a place sends, as a function of the four things that sentAtPlace reads. -/
def sentBy (sh : ReqShape) (lin : LinShape) (Pp : Option P1K2.Prep)
    (five : List (Array OracleNotice)) (a : Place) : List (Array OracleNotice) :=
  match a.kind, a.link with
  | .K1, some l =>
    if a.piece = 1 then [firstOn sh] else [laterOn sh l (if a.piece ≤ 5 then 1 else 2)]
  | .K1, none => ((linMessageW lin).map fun msg => wOn msg).toList
  | .K2, link => ((Pp.bind fun P => P1K2.numsAt P link).map (·.sent)).toList
  | .K12, _ => five
  | _, _ => []

theorem sent_by (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) :
    sentAtPlace Z G a = sentBy G.first.shape G.first.lin (P1K2.prepOf Z G)
      (K12.Coin.sendsFrom (H2U.p12OfMade Z.made) 0 (H2U.p12OfMade Z.made).nums.stages.tail) a := by
  rcases a with ⟨ch, link, piece, kind⟩
  cases kind <;> cases link <;> rfl

theorem prepareAt_on {z : ProofSized} {W : Model.Verify.Public} {first : Params.First} {c : Codes}
    {s : ReqShape} {n : Nat} (ht : P1K2.tied z first c s n = true) :
    P1K2.prepareAt z W first c s n = prepOn z first.shape.link.length := by
  unfold P1K2.prepareAt prepOn
  rw [ht]
  rfl

/-! ### The closed terms -/

/-- The written sized proof. -/
abbrev zW : ProofSized := proofSizedFull

/-- K2's numbers' ground at the written sized proof. -/
def prepW : Option P1K2.Prep := prepOn zW zW.request.link.length

/-- What number j sends, at the written terms, with K12's sendings as a letter. -/
def snBy (five : List (Array OracleNotice)) (j : Nat) : List (Array OracleNotice) :=
  match placesW[j]? with
  | some a => sentBy zW.request zW.batch.shape prepW five a
  | none => []

/-- The planner's written list of the first chain's sendings, as it is written. -/
def left0 : List (Array OracleNotice) :=
  Johnson.G.proofSendsFull.1.sends.map fun x => x.sent.toArray

def frontW : List (Array OracleNotice) := (List.range 354).flatMap (snBy [])
def backW : List (Array OracleNotice) := [355, 356, 357].flatMap (snBy [])

/-- The written list's 77th to 81st sendings. -/
def fiveW : List (Array OracleNotice) := (left0.drop 76).take 5

theorem sorted_written : Johnson.G.proofSendsFull.1.sends.Pairwise
    (fun a b => (decide (a.entry ≤ b.entry)) = true) := by decide +kernel

theorem front_len : frontW.length = 76 := by decide +kernel

/-- **The closed equation, by the kernel.** -/
theorem closed_but_354 : left0 = frontW ++ (fiveW ++ backW) := by decide +kernel

/-- The equation can fail: with the five taken one place earlier it is false. -/
theorem closed_can_fail : ¬ (left0 = frontW ++ ((left0.drop 75).take 5 ++ backW)) := by decide +kernel

theorem no_k12 : ∀ j < 358, j ≠ 354 → (placesW[j]?.map (·.kind)) ≠ some KindName.K12 := by
  decide +kernel

theorem k12_sits_354 : placesW[354]? = some ⟨1, none, 2, .K12⟩ := by decide +kernel

theorem samples_written : zW.set.samples = zW.request.answers := by decide +kernel

theorem snBy_free (five : List (Array OracleNotice)) {j : Nat} (hj : j < 358) (h : j ≠ 354) :
    snBy five j = snBy [] j := by
  have hk := no_k12 j hj h
  unfold snBy
  cases hp : placesW[j]? with
  | none => rfl
  | some a =>
    rw [hp] at hk
    rcases a with ⟨ch, link, piece, kind⟩
    cases kind <;> cases link <;> first | rfl | exact absurd rfl hk

theorem snBy_354 (five : List (Array OracleNotice)) : snBy five 354 = five := by
  unfold snBy
  rw [k12_sits_354]
  rfl

theorem flatMap_agree {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem flat_by (five : List (Array OracleNotice)) :
    (List.range 358).flatMap (snBy five) = frontW ++ (five ++ backW) := by
  have e : List.range 358 = List.range 354 ++ (354 :: [355, 356, 357]) := by decide +kernel
  rw [e, List.flatMap_append, List.flatMap_cons, snBy_354]
  have h1 : (List.range 354).flatMap (snBy five) = frontW :=
    flatMap_agree fun j hj => by
      have := List.mem_range.mp hj
      exact snBy_free five (by omega) (by omega)
  have h2 : [355, 356, 357].flatMap (snBy five) = backW :=
    flatMap_agree fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact snBy_free five (by omega) (by omega)
  rw [h1, h2]

/-! ### The pins -/

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem pins (hy : madeRow Z = true) :
    Z.p.chains.made.sized.proof = zW ∧ Z.first.shape = zW.request ∧
      Z.first.lin = zW.batch.shape ∧ Z.first.codes = zW.codes ∧
      Z.made.proof = Johnson.G.proofSendsFull := by
  unfold madeRow at hy
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hy
  unfold madeIs at h1
  simp only [Bool.and_eq_true] at h1
  unfold firstIs at h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨sameProof_eq h1.1, h2.1.1.1.2, h2.1.1.1.1.2, h2.1.1.1.1.1, proofSends_of_is h3⟩

theorem prep_pinned (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hy : madeRow Z = true)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    P1K2.prepOf Z G = prepW := by
  obtain ⟨hz, hsh, -, hco, -⟩ := pins hy
  have hf : G.first = Z.first := Meaning.K2.blank_first hG
  have hs := Meaning.K2.pub_start h
  unfold S.startP at hs
  split at hs
  · rename_i hok
    have e := Option.some.inj hs
    unfold S.startOk at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    have ht : P1K2.tied Z.p.chains.made.sized.proof G.first Z.s₀.st.codes
        Z.s₀.check.frame.shape Z.P.samples = true := by
      rw [← e, hf, hz]
      unfold P1K2.tied
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨⟨hsh.symm, hco.symm⟩, hco⟩, hsh⟩, by rw [samples_written, ← hsh]; exact hok.2.1.2⟩
    unfold P1K2.prepOf
    rw [prepareAt_on ht, hz, hf, hsh]
    rfl
  · cases hs

theorem sn_pinned (O : Open o pol lay KL F Z Bs base c A B) (hy : madeRow Z = true) (j : Nat) :
    snAt Z Bs.G₀ placesW j = snBy (K12.Coin.sendsFrom (H2U.p12OfMade Z.made) 0
      (H2U.p12OfMade Z.made).nums.stages.tail) j := by
  obtain ⟨-, hsh, hlin, -, -⟩ := pins hy
  have hf : Bs.G₀.first = Z.first := Meaning.K2.blank_first O.blank
  unfold snAt snBy
  cases placesW[j]? with
  | none => rfl
  | some a =>
    show sentAtPlace Z Bs.G₀ a = _
    rw [sent_by, prep_pinned O.pub hy O.blank, hf, hsh, hlin]

theorem left_pinned (hy : madeRow Z = true) :
    ((Z.made.proof.1.sends.mergeSort fun a b => a.entry ≤ b.entry).map fun x => x.sent.toArray) =
      left0 := by
  rw [(pins hy).2.2.2.2]
  unfold left0
  rw [List.mergeSort_of_pairwise sorted_written]

/-- **The 77 numbers that send, but K12's.** -/
theorem sends_but_354 (O : Open o pol lay KL F Z Bs base c A B) (hy : madeRow Z = true) :
    SendsAre Z.made.proof.1 358 (fun j => if j = 354 then fiveW else snAt Z Bs.G₀ placesW j) := by
  unfold SendsAre
  rw [left_pinned hy, closed_but_354, ← flat_by fiveW]
  refine (flatMap_agree fun j hj => ?_).symm
  have hj' := List.mem_range.mp hj
  by_cases h : j = 354
  · subst h
    rw [if_pos rfl, snBy_354]
  · rw [if_neg h, sn_pinned O hy, snBy_free _ hj' h, snBy_free fiveW hj' h]

/-- **The test accepts, where K12's five sendings are the written five.** -/
theorem sends_pinned (O : Open o pol lay KL F Z Bs base c A B) (hy : madeRow Z = true)
    (h354 : K12.Coin.sendsFrom (H2U.p12OfMade Z.made) 0 (H2U.p12OfMade Z.made).nums.stages.tail =
      fiveW) : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true := by
  unfold sendsAreB
  rw [decide_eq_true_eq, left_pinned hy, funext (sn_pinned O hy), h354, flat_by]
  exact closed_but_354

end IM

#print axioms IM.sent_by
#print axioms IM.prepareAt_on
#print axioms IM.sorted_written
#print axioms IM.closed_but_354
#print axioms IM.closed_can_fail
#print axioms IM.flat_by
#print axioms IM.pins
#print axioms IM.prep_pinned
#print axioms IM.sn_pinned
#print axioms IM.left_pinned
#print axioms IM.sends_but_354
#print axioms IM.sends_pinned
