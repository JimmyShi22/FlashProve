-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountTestsFill.lean: THE TWO PROXIMITY TESTS OF A PROOF FILE's SHARED CHAIN AT THE LEDGER's CLAUSE
(Johnson/Desc/Sound/SharedJointCountTests.lean: clause_of_test), AT THE TERMS OF THE ROW's SEVENTH FORM (SharedJointCountRowH.lean: the table's
meaningSigS, promSigS and its one extractor, handed the acting part's value: e₀H): THREE OF THE RULE's DEBTS ARE PAID THERE.

THE LETTERS, FILLED. M := a message for each member of a sending (Tup) · rg w := the witness's messages (msgsOf, MsgSig.lean) · Cand mu v m := at every
member of ms that sits at mu's tenant: CandAt, WordsLaw.lean (the library's OMsg.Cand: in the word's list, with the answers of the sample that the record
holds), at the oracles that the acting part's value shows · Same mu m m' := m and m' are one at these members.
  msgs_of_pin_cand   inside "no collision" a witness that is pinned at a member has the member's candidate there: by the library's sig_dec_good
                     (at a seed without a collision the decoder returns m just where m is a candidate).
  hdet_sig    PAID: a member's pin binds: from "no collision" at that message in the table's promise at the border.
  hlaid_sig   PAID: the laid witness has the pin: by dec_of_cand (WordsLaw.lean) and pin_ext (World.lean); under: a member sits at the tenant · the table lays that
              message at the block · no two of the block's own members have one number (tests on the plan's numbers).
  hctx_sig    PAID BUT FOR THE RIDING BACK: past the extractor by extSSame and pin_congr, under the test apartAt; that the pin comes back
              past the BLOCK (the record's sample and the tree's leaves stay) is the premise hback.
  clause_of_test_sig   the rule with these three laid in.
  nine_split_sig · nine_whole_sig · ten_sig   at the table's three rows: the table's own facts by evaluation.
WHAT STAYS, AND WHOSE, at each of the three: law (the kind's files: THE ONE DEBT WITH CHANCE IN IT) · hrow, hcong (the files that lay the rows; asked inside the promise; hcong under agreement at the laid and every kept message) · prom ·
frames (block 9 with a split alone: four items) · hback (the pins' files) · on the plan's numbers: a member sits at the laid tenant; no two of the
block's own have one number; apartAt at the kept message.

Every "there is", walked. In law: the tuple m: no verifier reads it. In the pin: "a member of ms sits there": a premise on the plan.
Limits. RULES: NO MEMBER IS SHOWN; smp₂, ms, arr, decT₂ are letters: UNTIL smp₂ HAS AN HONEST FILLING EVERY PIN HOLDS OF NOTHING. No block's text is
read. IT CLOSES NO ROW. NO SOUNDNESS. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountTests
import Johnson.Desc.Sound.SharedJointCountRowH
import Johnson.Desc.Sound.WordsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Doomed)
open VerifiableInference.Desc.Shared

section
variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **Inside "no collision" a pinned witness has the candidate.** -/
theorem msgs_of_pin_cand (x : Mem) (a : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (m : ((sigOf cs x.1.l).om x.2).Msg)
    (hp : CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y) (hc : CandAt cs G smp x a y m)
    (hw : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w) :
    msgsOf cs x.1.l x.1.seat arr w x.2 = m := by
  obtain ⟨z, hz, -, hn⟩ := hp
  obtain ⟨z', hz', hm⟩ := hc
  obtain ⟨z'', hz'', -, hd''⟩ := hw
  have ez : z' = z := Option.some.inj (hz'.symm.trans hz)
  have ez'' : z'' = z := Option.some.inj (hz''.symm.trans hz)
  rw [ez] at hm
  rw [ez''] at hd''
  have hd : ((sigOf cs x.1.l).om x.2).dec (wordsOf G cs x.1.l x.1.seat y x.2) z = some m :=
    (sig_dec_good GE _ _ z.1 hn z.2 m).2 hm
  exact Option.some.inj (hd''.symm.trans hd)

end

section
variable (cs : OnBytes.Codes) {Xi S₂ P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
  (stOf : S₂ → OnBytes.Statement) (bookOf : S₂ → OnBytes.TreeBook)
  (Ns : NumbersS) (Mg : MeaningS S₂ P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (Oc : P₁ → Strs → Prop) (split : Bool) {C : CK} {Fr : Frame}
  (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
  (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))

/-- A message for each member of a sending. -/
abbrev Tup : Type := (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg

/-- The witness's messages. -/
def rgT (w : Wit Cells Tok MsgT) : Tup cs := fun x => msgsOf cs x.1.l x.1.seat arr w x.2

/-- At every member that sits at the message's tenant the tuple has a candidate. -/
def candT (μ : Msg2) (v : ActV S₂ Fr) (m : Tup cs) : Prop :=
  ∀ x ∈ ms, SitsAt x (Ns.tenant μ).1 (Ns.tenant μ).2 →
    CandAt cs G smp₂ x v.1 (strsOfAct Fr v) (m x)

/-- Two tuples are one at the members that sit at the message's tenant. -/
def sameT (μ : Msg2) (m m' : Tup cs) : Prop :=
  ∀ x ∈ ms, SitsAt x (Ns.tenant μ).1 (Ns.tenant μ).2 → m' x = m x

/-- **A member's pin binds.** -/
theorem hdet_sig (k : ℕ) (μ : Msg2) (hμ : PromS.noColl μ ∈ promsAt split k)
    (a : (P₁ × S₂) × Fr.E.Str) (m : Tup cs) (w : Wit Cells Tok MsgT)
    (ha : onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a)
    (hc : candT cs G smp₂ ms Ns μ ((actQ Ns p l k).2 a) m)
    (hw : muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin μ) k ((actQ Ns p l k).2 a) w) :
    sameT cs ms Ns μ m (rgT cs arr w) := by
  intro x hx hs
  have hnc : noCollJT cs G smp₂ ms (Ns.tenant μ).1 (Ns.tenant μ).2 ((actQ Ns p l k).2 a).1
      (strsOfAct Fr ((actQ Ns p l k).2 a)) := by
    first
      | exact (ha.1 (.noColl μ) hμ).2.2
      | exact (ha.1 (.noColl μ) hμ).2
  have hcf := hnc x hx hs
  have hpin : pinJT cs G arr smp₂ ms (Ns.tenant μ).1 (Ns.tenant μ).2 ((actQ Ns p l k).2 a).1
      (strsOfAct Fr ((actQ Ns p l k).2 a)) w := hw
  exact msgs_of_pin_cand cs G arr smp₂ x _ _ w (m x) hcf (hc x hx hs) (hpin.2 x hx hs)

/-- A member that sits at the tenant of a message that the block lays is one of the block's own. -/
theorem mem_mineS (k : ℕ) (μ : Msg2) (hl : Comp.msg μ ∈ laysAtS split k) (x : Mem) (hx : x ∈ ms)
    (hs : SitsAt x (Ns.tenant μ).1 (Ns.tenant μ).2) : x ∈ mineS Ns ms split k := by
  refine List.mem_filter.2 ⟨hx, List.any_eq_true.2 ⟨.msg μ, hl, ?_⟩⟩
  have e : x.1.seat x.2 = Ns.tenant μ := hs
  exact decide_eq_true e

/-- **The laid witness has the pin.** -/
theorem hlaid_sig (k : ℕ) (μ : Msg2) (hμ : PromS.noColl μ ∈ promsAt split k)
    (hl : Comp.msg μ ∈ laysAtS split k)
    (hsit : ∃ x ∈ ms, SitsAt x (Ns.tenant μ).1 (Ns.tenant μ).2)
    (hN : ((mineS Ns ms split k).map (numOf arr)).Nodup)
    (a : (P₁ × S₂) × Fr.E.Str) (m : Tup cs) (w : Wit Cells Tok MsgT)
    (ha : onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a)
    (hc : candT cs G smp₂ ms Ns μ ((actQ Ns p l k).2 a) m) :
    muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin μ) k ((actQ Ns p l k).2 a)
      (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr k ((actQ Ns p l k).2 a) w) := by
  show pinJT cs G arr smp₂ ms (Ns.tenant μ).1 (Ns.tenant μ).2 ((actQ Ns p l k).2 a).1
    (strsOfAct Fr ((actQ Ns p l k).2 a))
    (extAt cs G arr smp₂ decT₂ c₀ (mineS Ns ms split k) [] ((laysAtS split k).contains .cells) none
      ((actQ Ns p l k).2 a).1 (strsOfAct Fr ((actQ Ns p l k).2 a)) w)
  refine ⟨hsit, fun x hx hs => ?_⟩
  have hnc : noCollJT cs G smp₂ ms (Ns.tenant μ).1 (Ns.tenant μ).2 ((actQ Ns p l k).2 a).1
      (strsOfAct Fr ((actQ Ns p l k).2 a)) := by
    first
      | exact (ha.1 (.noColl μ) hμ).2.2
      | exact (ha.1 (.noColl μ) hμ).2
  have hcf := hnc x hx hs
  refine pin_ext cs G arr smp₂ decT₂ c₀ (mineS Ns ms split k) [] _ none _ _ w x
    (mem_mineS ms Ns split k μ hl x hx hs) _
    (dec_of_cand cs G smp₂ x _ _ (m x) hcf (hc x hx hs))
    (agree_of_nodup cs G arr smp₂ _ hN _ _ _) ?_
  rw [List.append_nil]
  exact agreeSeat_of_nodup cs G arr smp₂ _ hN _ _ _

/-- **A kept member's pin comes past the extractor.** -/
theorem pin_past_ext (k : ℕ) (ν : Msg2) (hnl : Comp.msg ν ∉ laysAtS split k)
    (hap : apartAt Ns arr split k (.msg ν) = true) (v : ActV S₂ Fr) (w : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp₂ ms (Ns.tenant ν).1 (Ns.tenant ν).2 v.1 (strsOfAct Fr v) w) :
    pinJT cs G arr smp₂ ms (Ns.tenant ν).1 (Ns.tenant ν).2 v.1 (strsOfAct Fr v)
      (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr k v w) := by
  have hs : sameAt Ns arr (.msg ν) (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr k v w) w :=
    extSSame cs Xi S₂ Cells Tok G arr smp₂ ms decT₂ c₀ Ns split k (.msg ν) hnl hap v.1
      (strsOfAct Fr v) w
  refine ⟨h.1, fun x hx hsit => ?_⟩
  have e : x.1.seat x.2 = ((Ns.tenant ν).1, (Ns.tenant ν).2) := hsit
  refine pin_congr cs G arr smp₂ x.1 x.2 v.1 (strsOfAct Fr v) w _ ?_ ?_ (h.2 x hx hsit)
  · rw [e]
    exact hs.1
  · rw [e]
    exact hs.2

variable (Say : S₂ → RowS → Tup cs → Prop)

/-- **A proximity test at the ledger's clause, at the seventh form's terms.** -/
theorem clause_of_test_sig (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (ε : Err (uLT C x.ds)) (laid : Msg2) (kept : List Msg2) (cls : List RowS)
    (hins : ∀ i, insSh split k i →
      i = .pin laid ∨ (∃ ν ∈ kept, i = .pin ν) ∨ ∃ c ∈ cls, i = .row c)
    (houts : ∀ ν ∈ kept, outsSh split k (.pin ν))
    (hnc : ∀ μ, μ = laid ∨ μ ∈ kept → PromS.noColl μ ∈ promsAt split k)
    (hl : Comp.msg laid ∈ laysAtS split k) (hnl : ∀ ν ∈ kept, Comp.msg ν ∉ laysAtS split k)
    (hsit : ∃ y ∈ ms, SitsAt y (Ns.tenant laid).1 (Ns.tenant laid).2)
    (hN : ((mineS Ns ms split k).map (numOf arr)).Nodup)
    (hap : ∀ ν ∈ kept, apartAt Ns arr split k (.msg ν) = true)
    (law : x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k)
      (fun a _ => TestSays Ns p l Say (candT cs G smp₂ ms Ns) k laid kept cls a) ε)
    (hback : ∀ ν ∈ kept, ∀ a τ b w,
      onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a →
      x.ior.red.out a τ = some b →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin ν) (k + 1)
        ((actQ Ns p l (k + 1)).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin ν) k ((actQ Ns p l k).2 a) w)
    (hrow : ∀ c ∈ cls, ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a → ∀ w,
      Say a.1.2 c (rgT cs arr w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ cls, ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a → ∀ m m',
      (∀ μ, μ = laid ∨ μ ∈ kept → sameT cs ms Ns μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a →
      x.ior.red.out a τ = some b →
      promQ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) split p l (k + 1)
        ((actQ Ns p l (k + 1)).2 b))
    (frames : ∀ a τ b w i, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k a →
      x.ior.red.out a τ = some b →
      openAfter (insSh split) (outsSh split) startSh k i → ¬ insSh split k i →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i (k + 1) ((actQ Ns p l (k + 1)).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i k ((actQ Ns p l k).2 a)
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr k ((actQ Ns p l k).2 a) w)) :
    x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l k)
      (fun a b => stepV Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg)
        (promSigS cs G smp₂ ms stOf bookOf Pm) split p l
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr) k ((actQ Ns p l k).2 a)
        ((actQ Ns p l (k + 1)).2 b)) ε :=
  clause_of_test Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm)
    Oc split p l (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr) (rgT cs arr) Say
    (candT cs G smp₂ ms Ns) (sameT cs ms Ns) k x ε laid kept cls hins houts law
    (fun μ hμ a m w ha hc hw =>
      hdet_sig cs G arr smp₂ ms decT₂ stOf bookOf Ns Mg Pm Oc split p l k μ (hnc μ hμ) a m w ha hc
        hw)
    (fun a m w ha hc =>
      hlaid_sig cs G arr smp₂ ms decT₂ c₀ stOf bookOf Ns Mg Pm Oc split p l k laid
        (hnc laid (Or.inl rfl)) hl hsit hN a m w ha hc)
    (fun ν hν a τ b w ha hb hw =>
      pin_past_ext cs G arr smp₂ ms decT₂ c₀ Ns split k ν (hnl ν hν) (hap ν hν) _ w
        (hback ν hν a τ b w ha hb hw))
    hrow hcong prom frames

/-! ## At the table's three rows -/

/-- **Block 9, with a split, at the seventh form's terms.** -/
theorem nine_split_sig (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT C x.ds))
    (hsit : ∃ y ∈ ms, SitsAt y (Ns.tenant .oU).1 (Ns.tenant .oU).2)
    (hN : ((mineS Ns ms true 9).map (numOf arr)).Nodup)
    (hap : apartAt Ns arr true 9 (.msg .oSp) = true)
    (law : x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9)
      (fun a _ => TestSays Ns p l Say (candT cs G smp₂ ms Ns) 9 .oU [.oSp]
        [.sample .oU, .recG, .loc, .foldU] a) ε)
    (hback : ∀ a τ b w, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9 a →
      x.ior.red.out a τ = some b →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oSp) 10 ((actQ Ns p l 10).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oSp) 9 ((actQ Ns p l 9).2 a) w)
    (hrow : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9 a → ∀ w,
      Say a.1.2 c (rgT cs arr w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9 a → ∀ m m',
      (∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] → sameT cs ms Ns μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9 a →
      x.ior.red.out a τ = some b →
      promQ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) true p l 10 ((actQ Ns p l 10).2 b))
    (frames : ∀ i ∈ [ItemS.pin .oOmega, .row (.sample .oOmega), .row (.sample .oSp),
        .row .foldOmega], ∀ a τ b w,
      onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9 a →
      x.ior.red.out a τ = some b →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 10 ((actQ Ns p l 10).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 9 ((actQ Ns p l 9).2 a)
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns true Fr 9 ((actQ Ns p l 9).2 a) w)) :
    x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 9)
      (fun a b => stepV Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg)
        (promSigS cs G smp₂ ms stOf bookOf Pm) true p l
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns true Fr) 9 ((actQ Ns p l 9).2 a)
        ((actQ Ns p l 10).2 b)) ε :=
  clause_of_test_sig cs G arr smp₂ ms decT₂ c₀ stOf bookOf Ns Mg Pm Oc true p l Say 9 x ε .oU
    [.oSp] [.sample .oU, .recG, .loc, .foldU] ins_nine_split outs_nine_split
    (by
      intro μ hμ
      rcases hμ with rfl | hμ
      · decide
      · obtain rfl : μ = .oSp := by simpa using hμ
        decide)
    (by decide) (by decide) hsit hN
    (by
      intro ν hν
      obtain rfl : ν = .oSp := by simpa using hν
      exact hap)
    law
    (by
      intro ν hν
      obtain rfl : ν = .oSp := by simpa using hν
      exact hback)
    hrow hcong prom
    (fun a τ b w i ha hb ho hn hm => frames i (rides_nine_split i ho hn) a τ b w ha hb hm)

/-- **Block 9, without a split, at the seventh form's terms.** -/
theorem nine_whole_sig (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT C x.ds))
    (hsit : ∃ y ∈ ms, SitsAt y (Ns.tenant .oU).1 (Ns.tenant .oU).2)
    (hN : ((mineS Ns ms false 9).map (numOf arr)).Nodup)
    (hap : apartAt Ns arr false 9 (.msg .oOmega) = true)
    (law : x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9)
      (fun a _ => TestSays Ns p l Say (candT cs G smp₂ ms Ns) 9 .oU [.oOmega]
        [.sample .oU, .recG, .loc, .fold, .sample .oOmega] a) ε)
    (hback : ∀ a τ b w, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9 a →
      x.ior.red.out a τ = some b →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oOmega) 10
        ((actQ Ns p l 10).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oOmega) 9 ((actQ Ns p l 9).2 a) w)
    (hrow : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .fold, .sample .oOmega], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9 a → ∀ w,
      Say a.1.2 c (rgT cs arr w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oU, .recG, .loc, .fold, .sample .oOmega], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9 a → ∀ m m',
      (∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oOmega] → sameT cs ms Ns μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9 a →
      x.ior.red.out a τ = some b →
      promQ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) false p l 10 ((actQ Ns p l 10).2 b)) :
    x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc false p l 9)
      (fun a b => stepV Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg)
        (promSigS cs G smp₂ ms stOf bookOf Pm) false p l
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns false Fr) 9 ((actQ Ns p l 9).2 a)
        ((actQ Ns p l 10).2 b)) ε :=
  clause_of_test_sig cs G arr smp₂ ms decT₂ c₀ stOf bookOf Ns Mg Pm Oc false p l Say 9 x ε .oU
    [.oOmega] [.sample .oU, .recG, .loc, .fold, .sample .oOmega] ins_nine_whole outs_nine_whole
    (by
      intro μ hμ
      rcases hμ with rfl | hμ
      · decide
      · obtain rfl : μ = .oOmega := by simpa using hμ
        decide)
    (by decide) (by decide) hsit hN
    (by
      intro ν hν
      obtain rfl : ν = .oOmega := by simpa using hν
      exact hap)
    law
    (by
      intro ν hν
      obtain rfl : ν = .oOmega := by simpa using hν
      exact hback)
    hrow hcong prom (fun _ _ _ _ i _ _ ho hn _ => absurd (rides_nine_whole i ho) hn)

/-- **Block 10, at the seventh form's terms.** -/
theorem ten_sig (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))
    (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT C x.ds))
    (hsit : ∃ y ∈ ms, SitsAt y (Ns.tenant .oSp).1 (Ns.tenant .oSp).2)
    (hN : ((mineS Ns ms true 10).map (numOf arr)).Nodup)
    (hap : apartAt Ns arr true 10 (.msg .oOmega) = true)
    (law : x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10)
      (fun a _ => TestSays Ns p l Say (candT cs G smp₂ ms Ns) 10 .oSp [.oOmega]
        [.sample .oOmega, .sample .oSp, .foldOmega] a) ε)
    (hback : ∀ a τ b w, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10 a →
      x.ior.red.out a τ = some b →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oOmega) 11
        ((actQ Ns p l 11).2 b) w →
      muQ Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oOmega) 10
        ((actQ Ns p l 10).2 a) w)
    (hrow : ∀ c ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10 a → ∀ w,
      Say a.1.2 c (rgT cs arr w) → Mg.row c a.1.2 w)
    (hcong : ∀ c ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], ∀ a, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10 a → ∀ m m',
      (∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] → sameT cs ms Ns μ m m') → Say a.1.2 c m → Say a.1.2 c m')
    (prom : ∀ a τ b, onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10 a →
      x.ior.red.out a τ = some b →
      promQ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) true p l 11 ((actQ Ns p l 11).2 b)) :
    x.ior.red.Leads (onQ₂ Ns (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 10)
      (fun a b => stepV Ns (meaningSigS cs G arr smp₂ ms decT₂ Mg)
        (promSigS cs G smp₂ ms stOf bookOf Pm) true p l
        (e₀H cs G arr smp₂ ms decT₂ c₀ Ns true Fr) 10 ((actQ Ns p l 10).2 a)
        ((actQ Ns p l 11).2 b)) ε :=
  clause_of_test_sig cs G arr smp₂ ms decT₂ c₀ stOf bookOf Ns Mg Pm Oc true p l Say 10 x ε .oSp
    [.oOmega] [.sample .oOmega, .sample .oSp, .foldOmega] ins_ten outs_ten
    (by
      intro μ hμ
      rcases hμ with rfl | hμ
      · decide
      · obtain rfl : μ = .oOmega := by simpa using hμ
        decide)
    (by decide) (by decide) hsit hN
    (by
      intro ν hν
      obtain rfl : ν = .oOmega := by simpa using hν
      exact hap)
    law
    (by
      intro ν hν
      obtain rfl : ν = .oOmega := by simpa using hν
      exact hback)
    hrow hcong prom (fun _ _ _ _ i _ _ ho hn _ => absurd (rides_ten i ho) hn)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.msgs_of_pin_cand
#print axioms VerifiableInference.Desc.Sound.hdet_sig
#print axioms VerifiableInference.Desc.Sound.hlaid_sig
#print axioms VerifiableInference.Desc.Sound.pin_past_ext
#print axioms VerifiableInference.Desc.Sound.clause_of_test_sig
#print axioms VerifiableInference.Desc.Sound.nine_split_sig
#print axioms VerifiableInference.Desc.Sound.nine_whole_sig
#print axioms VerifiableInference.Desc.Sound.ten_sig
