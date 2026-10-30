-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameCarryBack.lean: THE CARRIED WORD's SENTENCE, AS IT IS FILLED
(`K2Caller.carryAtZ`, Johnson/Top/H0/K2Caller/CarryClosed.lean: the way
in `doorZ`, whose `rest` lays the copy's flag "a link is under way" to false), GOES BACK
OVER THE STEPS OF ITS SPAN, at a segment whose switch stands at a link: one rule, and three steps
that have its premise: an accepting "cleared"; "the segment is shut"; a step that leaves the
verifier's state. Statements and proofs.


What is said.
  `StLike S S'`: two statements with the same codes, groups and number of oracle messages, and the
    same oracle messages but for their ledgers.
  `firstFront_like`: the front's maker answers at both or at neither; the two fronts part in their
    statements alone, and these are `StLike`.
  `frameAt_like`, `smpK2_like`, `bookAt_like`, `longFront_like`: the frame at a front, the held OOD
    samples, the book behind the sending and the carried rows' symbols off the oracles read of the
    front's statement nothing that `StLike` lets part.
  `carryRow_like`: **so `carryRow` at a place that stands at a link holds at a state u wherever it
    holds at a state t with the same walk's copy's frame, book and number of roots and a statement
    that is `StLike`**, where the carried rows' symbols off the two families of oracles are the
    same.
  `RestLike s t`: WHAT A STEP OWES: what the way in lets in of s and of t are such a pair.
  `carry_back_of`: **THE RULE: `carryAtZ Z lay m (p, t) y' w → carryAtZ Z lay m (p, s) y w`** under
    `RestLike s t`, at m with `(ProofFile.pAtK2 Z m).stands = .link`.
  `rest_cleared`, `restLike_cleared`, `carry_back_cleared`: an accepting "cleared" has `RestLike`
    (with a row left or without).
  `restLike_shut`: the closing's third sub-protocol, "the segment is shut"
    (Johnson/Desc/First/Batch/Place.lean), has it.
  `CarryFence Z m base u`: THE FENCE, on numbers: every tree in which the book behind the switch's
    sending places a message of the carried rows has, in the frame's list, a number below base.
  `orcY_stays`, `longFront_stays`: under the fence and `Stays` the carried rows' symbols are the
    same off both families of oracles.
  `carry_goesBack_of`, `carry_goesBack_cleared`, `carry_goesBack_same`: **the rule as
    `GoesBack (StepRel rel base In) (carryAtZ Z lay m)`**, general in In, which is spent once: In
    gives the fence at `rest s`.

Limits. THE FENCE IS A PREMISE: that what is known in front of a step gives it is not shown here: no
text that the sentence runs through refuses a book in which a tree's number is bent: it wants a fact
on reached states. The places that stand at the head and at the finish are not treated. Whether the
sentence can be met is not shown. No soundness statement.

-/
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Top.H0.Walk.FrameFieldsBack
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (GoesBack)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 frontAt longFront bookAt openedOne colOne_congr par9
  SameShapes frame_congr frameAt skelOf idsOf)
open VerifiableInference.Desc.First.K2Hands (samplesOf)
open VerifiableInference.Desc.Ground (newGroupP newGroupL groupL withGroup)
open VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First.Pend (pendingRowO)
open _root_.Tw.K2 (firstFront Front switchNotices)

/-- The same statement but for the oracle messages' ledgers. -/
structure StLike (S₁ S₂ : Statement) : Prop where
  codes : S₂.codes = S₁.codes
  groups : S₂.groups = S₁.groups
  size : S₂.oracles.size = S₁.oracles.size
  msgs : ∀ i : Nat, (S₂.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
    (S₁.oracles[i]?).map fun (x : Oracle) => { x with ledger := none }

namespace StLike
variable {S₁ S₂ : Statement} (h : StLike S₁ S₂)
include h

theorem shape (o : Nat) :
    (S₂.oracles[o]?).map (·.shape) = (S₁.oracles[o]?).map (·.shape) := by
  have h1 := congrArg (Option.map fun a : Oracle => a.shape) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  exact h1

theorem rows (o : Nat) : (S₂.oracles.getD o default).sampleRows =
    (S₁.oracles.getD o default).sampleRows := by
  have h1 := congrArg (Option.map fun a : Oracle => a.sampleRows) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases e1 : S₂.oracles[o]? <;> cases e2 : S₁.oracles[o]? <;> simp [e1, e2] at h1 ⊢
  exact h1

theorem sameShapes : SameShapes S₁ S₂ := ⟨h.codes, h.shape⟩

/-- With the same notices received. -/
theorem sent (n : Array OracleNotice) :
    SameShapes (OnBytes.Slice.stSent S₁ n) (OnBytes.Slice.stSent S₂ n) := by
  refine ⟨h.codes, fun o => ?_⟩
  unfold OnBytes.Slice.stSent
  dsimp only
  by_cases ho : o < S₁.oracles.size
  · rw [Array.getElem?_append_left ho, Array.getElem?_append_left (by rw [h.size]; exact ho)]
    exact h.shape o
  · have k1 : S₁.oracles.size ≤ o := by omega
    have k2 : S₂.oracles.size ≤ o := by rw [h.size]; exact k1
    rw [Array.getElem?_append_right k2, Array.getElem?_append_right k1, h.size]

end StLike

/-- What a yes of "one more group" says. -/
theorem newGroupG_ok {S₀ S' : Statement} {c m g : Nat}
    (h : _root_.Tw.K2.newGroupG S₀ c m = .ok (S', g)) :
    VerifiableInference.Desc.Ground.ok (groupL S₀.codes c m) = true ∧ S' = withGroup S₀ c m ∧
      g = S₀.groups.size := by
  unfold _root_.Tw.K2.newGroupG newGroupP newGroupL _root_.Tw.K2.dOf at h
  dsimp only at h
  by_cases hk : VerifiableInference.Desc.Ground.ok (groupL S₀.codes c m) = true
  · rw [if_pos hk] at h
    dsimp only at h
    cases h
    exact ⟨hk, rfl, rfl⟩
  · rw [if_neg hk] at h
    cases h

theorem newGroupG_of {S₀ : Statement} {c m : Nat}
    (hk : VerifiableInference.Desc.Ground.ok (groupL S₀.codes c m) = true) :
    _root_.Tw.K2.newGroupG S₀ c m = .ok (withGroup S₀ c m, S₀.groups.size) := by
  unfold _root_.Tw.K2.newGroupG newGroupP newGroupL _root_.Tw.K2.dOf
  dsimp only
  rw [if_pos hk]

/-- **The front's maker at two such statements.** -/
theorem firstFront_like {S₁ S₂ : Statement} (h : StLike S₁ S₂) (f : ReqFrame) {x : Front}
    (hx : firstFront S₁ f = .ok x) :
    ∃ x', firstFront S₂ f = .ok x' ∧ x'.f = x.f ∧ x'.own = x.own ∧ x'.others = x.others ∧
      x'.T = x.T ∧ x'.plain = x.plain ∧ StLike x.st x'.st := by
  unfold firstFront at hx ⊢
  split at hx
  · cases hx
  · rename_i h1
    rw [if_neg h1]
    split at hx
    · cases hx
    · rename_i h2
      rw [if_neg h2]
      split at hx
      · rename_i L G hL hG
        dsimp only at hx ⊢
        cases hg : _root_.Tw.K2.newGroupG S₁ f.shape.code f.shape.maskCode with
        | error e =>
          rw [hg] at hx
          cases hx
        | ok z =>
          obtain ⟨S', g⟩ := z
          rw [hg] at hx
          dsimp only at hx
          obtain ⟨hk, rfl, rfl⟩ := newGroupG_ok hg
          rw [newGroupG_of (by rw [h.codes]; exact hk)]
          dsimp only
          obtain rfl : _ = x := Except.ok.inj hx
          refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
          · dsimp only
            rw [h.groups]
          · exact ⟨h.codes, by
              show (S₂.groups.push _) = (S₁.groups.push _)
              rw [h.groups], h.size, h.msgs⟩
      · cases hx
      · cases hx

theorem skel_like {x x' : Front} (ho : x'.others = x.others) (hT : x'.T = x.T)
    (hs : StLike x.st x'.st) : SameShapes (skelOf x) (skelOf x') := by
  unfold skelOf
  rw [hT, ho]
  exact hs.sent _

theorem frameAt_like {x x' : Front} (hf : x'.f = x.f) (ho : x'.others = x.others)
    (hT : x'.T = x.T) (hs : StLike x.st x'.st) : frameAt x' = frameAt x := by
  unfold frameAt
  rw [frame_congr (skel_like ho hT hs)]
  unfold idsOf
  rw [hf, hT, ho, hs.size]

theorem smpK2_like {x x' : Front} (hs : StLike x.st x'.st) (r : SwRow) (H : r.OK)
    (W : SwitchFrame) : smpK2 r H x' W = smpK2 r H x W := by
  have e : ∀ k, rowK2 r H x'.st W k = rowK2 r H x.st W k := by
    intro k
    unfold rowK2 samplesOf
    rw [hs.rows]
  have e1 : rowK2 r H x'.st W = rowK2 r H x.st W := funext e
  have e2 : FitsK2 r H x'.st W = FitsK2 r H x.st W := by
    funext k sd
    unfold FitsK2
    rw [e]
  funext k
  unfold smpK2
  rw [e1, e2]

theorem bookAt_like {S₁ S₂ : Statement} (hs : StLike S₁ S₂) (ft : Nat) (B : TreeBook)
    (roots : Nat) (n : Array OracleNotice) : bookAt ft S₂ B roots n = bookAt ft S₁ B roots n := by
  unfold bookAt VerifiableInference.Desc.Ground.recvP VerifiableInference.Desc.Ground.recvL
  dsimp only
  rw [hs.codes, hs.size]
  split
  · rw [Option.map_map, Option.map_map]
    rfl
  · rfl

theorem longFront_like {x x' : Front} (hf : x'.f = x.f) (ho : x'.others = x.others)
    (hT : x'.T = x.T) (hs : StLike x.st x'.st) (p : P2) {u t : S} (hb : t.book = u.book)
    (hr : t.roots = u.roots) (orc : Nat → Nat → List UInt64) (q : Nat) :
    longFront p u x' orc q = longFront p t x orc q := by
  unfold longFront
  rw [bookAt_like hs, hf, hT, ho, hb, hr]
  have e : ∀ (B : TreeBook) (idp : Array (Nat × Nat × Nat)),
      openedOne (skelOf x') B (par9 p).firstTree p.logN orc idp q =
        openedOne (skelOf x) B (par9 p).firstTree p.logN orc idp q := by
    intro B idp
    unfold openedOne
    simp only [colOne_congr (skel_like ho hT hs)]
  simp only [e]

/-- **The sentence at a typed row, at two states that part in ledgers, in where the chain stands and
in what is put out.** -/
theorem carryRow_like (r : SwRow) (H : r.OK) {p : P2} (hp : p.stands = .link)
    (orc : Strs → ℕ → ℕ → List UInt64) {u t : S} (hc : u.check.frame = t.check.frame)
    (hb : t.book = u.book) (hr : t.roots = u.roots) (hs : StLike t.st u.st) {y y' : Strs}
    (hy : ∀ fx q, frontAt p u = some fx → longFront p u fx (orc y) q = longFront p u fx (orc y') q)
    (h : carryRow r H p orc (smpK2 r H) t y') : carryRow r H p orc (smpK2 r H) u y := by
  obtain ⟨fx, W₀, h1, h2, h3⟩ := h
  have h1' : (firstFront t.st t.check.frame).toOption = some fx := by
    unfold frontAt at h1
    rw [hp] at h1
    exact h1
  obtain ⟨fx0, e0⟩ : ∃ z, firstFront t.st t.check.frame = .ok z := by
    cases e : firstFront t.st t.check.frame with
    | error _ => rw [e] at h1'; cases h1'
    | ok z => exact ⟨z, rfl⟩
  obtain rfl : fx0 = fx := by
    rw [e0] at h1'
    exact Option.some.inj h1'
  obtain ⟨fx', e1, hf, -, ho, hT, -, hst⟩ := firstFront_like hs t.check.frame e0
  have hfu : frontAt p u = some fx' := by
    unfold frontAt
    rw [hp, hc, e1]
    rfl
  refine ⟨fx', W₀, hfu, by rw [frameAt_like hf ho hT hst]; exact h2, ?_⟩
  have ea : faAt r H p orc (smpK2 r H) (u, fx', W₀) y =
      faAt r H p orc (smpK2 r H) (t, fx0, W₀) y' := by
    unfold faAt
    simp only [hf, smpK2_like hst, hy fx' _ hfu, longFront_like hf ho hT hst p hb hr]
  unfold VerifiableInference.Desc.First.K2Hands.carryOf at h3 ⊢
  rw [ea]
  exact h3

/-- In front of and behind an accepting "cleared". -/
theorem rest_cleared {L : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    rest s = { s with check := { s.live with inLink := false }, here := .between } ∧
      rest t = t := by
  obtain ⟨F, hF⟩ := fork_of_clear h
  have hb := (clearedGives L counts left lay lin s t h).1
  constructor
  · unfold rest S.inLink
    rw [hF]
    rfl
  · refine rest_out t ?_
    unfold S.inLink S.fork?
    unfold S.atBetween at hb
    cases hh : t.here <;> simp [hh] at hb ⊢

/-- **What a step owes for the sentence**: what the way in lets in of the state in front and of the
state behind have one frame in the walk's copy, one book, one number of roots, and statements that
are `StLike`. -/
structure RestLike (s t : S) : Prop where
  frame : (rest s).check.frame = (rest t).check.frame
  book : (rest t).book = (rest s).book
  roots : (rest t).roots = (rest s).roots
  st : StLike (rest t).st (rest s).st

theorem RestLike.refl (s : S) : RestLike s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem RestLike_iff (s t : S) : RestLike s t ↔
    (rest s).check.frame = (rest t).check.frame ∧ (rest t).book = (rest s).book ∧
      (rest t).roots = (rest s).roots ∧ (rest s).st.codes = (rest t).st.codes ∧
      (rest s).st.groups = (rest t).st.groups ∧
      (rest s).st.oracles.size = (rest t).st.oracles.size ∧
      ∀ i : Nat, ((rest s).st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
        ((rest t).st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none } :=
  ⟨fun h => ⟨h.frame, h.book, h.roots, h.st.codes, h.st.groups, h.st.size, h.st.msgs⟩,
    fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- **THE RULE: THE CARRIED WORD's SENTENCE GOES BACK OVER EVERY STEP WITH `RestLike`**, at a
segment whose switch stands at a link. -/
theorem carry_back_of {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) {s t : S} (h : RestLike s t) {y y' : Strs}
    (hy : ∀ fx q, frontAt (ProofFile.pAtK2 Z m) (rest s) = some fx →
      longFront (ProofFile.pAtK2 Z m) (rest s) fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) q =
        longFront (ProofFile.pAtK2 Z m) (rest s) fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y') q)
    (p : P) (w : W) (hc : carryAtZ Z layF m (p, t) y' w) : carryAtZ Z layF m (p, s) y w := by
  rw [carryAtZ_iff] at hc ⊢
  obtain ⟨r, t', hr, hd, hok, hrow⟩ := hc
  have hd' : t' = rest t := by
    unfold doorZ at hd
    rw [hp] at hd
    exact (Option.some.inj hd).symm
  subst hd'
  exact ⟨r, rest s, hr, by unfold doorZ; rw [hp], hok,
    carryRow_like r _ hp _ h.frame h.book h.roots h.st hy hrow⟩

/-- An accepting "cleared" has it. -/
theorem restLike_cleared {L : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    RestLike s t := by
  obtain ⟨e1, e2⟩ := rest_cleared h
  obtain ⟨-, k2, -, k4, k5, -, -, -, k9, k10, k11, k12, -⟩ :=
    clearedGives L counts left lay lin s t h
  rw [RestLike_iff, e1, e2]
  exact ⟨by rw [k2], k4, k5, k9.symm, k10.symm, k11.symm, fun i => (k12 i).symm⟩

/-- The closing's third sub-protocol ("the segment is shut") has it. -/
theorem restLike_shut {Cl : Type} (p : VerifiableInference.Desc.K9.Where) (piece : Nat) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.shut (Cl := Cl) p piece).decide s rs gs = .ok t) :
    RestLike s t := by
  have h' : (do
      let L ← VerifiableInference.Desc.K9.there "K9.in-a-segment" s.link?
      pure (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) :
        Except String S) = .ok t := h
  cases hl : s.link? with
  | none =>
    rw [hl] at h'
    cases h'
  | some L =>
    rw [hl] at h'
    obtain rfl : s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame) = t :=
      Except.ok.inj h'
    rw [RestLike_iff]
    cases hh : s.here with
    | lay a =>
      simp [S.link?, hh] at hl
      subst hl
      simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh,
        VerifiableInference.Desc.K9.closed]
    | att a =>
      simp [S.link?, hh] at hl
      subst hl
      simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh,
        VerifiableInference.Desc.K9.closed]
    | head a =>
      simp [S.link?, hh] at hl
      obtain ⟨ho, rfl⟩ := hl
      simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh, ho,
        VerifiableInference.Desc.K9.closed]
    | between => simp [S.link?, hh] at hl
    | fin a => simp [S.link?, hh] at hl
    | mem a => simp [S.link?, hh] at hl

/-- **OVER AN ACCEPTING "cleared".** -/
theorem carry_back_cleared {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) {L : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    {y y' : Strs}
    (hy : ∀ fx q, frontAt (ProofFile.pAtK2 Z m) (rest s) = some fx →
      longFront (ProofFile.pAtK2 Z m) (rest s) fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) q =
        longFront (ProofFile.pAtK2 Z m) (rest s) fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y') q)
    (p : P) (w : W) (hc : carryAtZ Z layF m (p, t) y' w) : carryAtZ Z layF m (p, s) y w :=
  carry_back_of Z layF m hp (restLike_cleared h) hy p w hc

/-! ### the strings: from a fence on the trees' numbers -/

/-- The closed reading of the oracles at a key whose tree lies below base. -/
theorem orcY_stays {all : List OnBytes.Maker.LeftT} {key : ℕ → ℕ} {base : Nat} {y y' : Strs}
    (hy : Stays base y y') {k : ℕ}
    (hk : ∀ L, all.find? (fun L => key L.no == k) = some L → L.no < base) (x : ℕ) :
    VerifiableInference.Desc.First.K2.orcY all key y k x =
      VerifiableInference.Desc.First.K2.orcY all key y' k x := by
  unfold VerifiableInference.Desc.First.K2.orcY
  cases e : all.find? (fun L => key L.no == k) with
  | none => rfl
  | some L => exact (hy.2 L.no x (hk L e)).symm

/-- **The fence**: at a state u: every tree in which the book behind the switch's sending places a
message of the carried rows has, in the frame's list of trees, a number below base. -/
def CarryFence (Z : ProofFile.Pub) (m base : ℕ) (u : S) : Prop :=
  ∀ fx B places, frontAt (ProofFile.pAtK2 Z m) u = some fx →
    bookAt (par9 (ProofFile.pAtK2 Z m)).firstTree fx.st u.book u.roots
      (switchNotices fx.T fx.others) = some B →
    (singleRowsOracles fx.f.rows).mapM (fun o => B.place[o]?) = some places →
    ∀ z ∈ (singleRowsOracles fx.f.rows).zip places, ∀ tree, B.trees[z.2.1]? = some tree →
      ∀ L, (ProofFile.allAt Z).find?
          (fun L => ProofFile.keyAt Z L.no == tree.number - (par9 (ProofFile.pAtK2 Z m)).firstTree) = some L →
        L.no < base

/-- **Under the fence the carried rows' symbols are the same off both families of oracles.** -/
theorem longFront_stays {Z : ProofFile.Pub} {m base : ℕ} {u : S} (hF : CarryFence Z m base u)
    {y y' : Strs} (hy : Stays base y y') (fx : Front) (q : ℕ)
    (hfx : frontAt (ProofFile.pAtK2 Z m) u = some fx) :
    longFront (ProofFile.pAtK2 Z m) u fx
        (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) q =
      longFront (ProofFile.pAtK2 Z m) u fx
        (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y') q := by
  unfold longFront
  cases hB : bookAt (par9 (ProofFile.pAtK2 Z m)).firstTree fx.st u.book u.roots
      (switchNotices fx.T fx.others) with
  | none => rfl
  | some B =>
    simp only [Option.bind_some]
    cases hP : (singleRowsOracles fx.f.rows).mapM (fun o => B.place[o]?) with
    | none => rfl
    | some places =>
      simp only [Option.bind_some]
      congr 1
      unfold openedOne
      refine Array.map_congr_left fun z hz => ?_
      congr 2
      unfold VerifiableInference.Desc.First.K2.colOne
      cases ht : B.trees[z.2.1]? with
      | none => rfl
      | some tree =>
        cases hx : (skelOf fx).oracles[z.1]? with
        | none => rfl
        | some x =>
          dsimp only
          rw [orcY_stays hy (hF fx B places hfx hB hP z hz tree ht)]

/-- **THE RULE, AS A SENTENCE THAT GOES BACK**: over every step with `RestLike`, under the fence at
`rest s`, had from what is known in front. -/
theorem carry_goesBack_of {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) (rel : S → S → Prop)
    (hrel : ∀ s t, rel s t → RestLike s t) (base : Nat) (In : P × S → Strs → Prop)
    (hF : ∀ p s y, In (p, s) y → CarryFence Z m base (rest s)) :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) := by
  intro a y b y' w hr hb
  obtain ⟨p, s⟩ := a
  obtain ⟨p', t⟩ := b
  obtain ⟨e, hc, hy, hI⟩ := hr
  obtain rfl : p' = p := e
  exact carry_back_of Z layF m hp (hrel s t hc)
    (fun fx q hfx => longFront_stays (hF p' s y hI) hy fx q hfx) p' w hb

/-- **Over an accepting "cleared".** -/
theorem carry_goesBack_cleared {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (base : Nat)
    (In : P × S → Strs → Prop) (hF : ∀ p s y, In (p, s) y → CarryFence Z m base (rest s)) :
    GoesBack (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In)
      (carryAtZ (P := P) (W := W) Z layF m) :=
  carry_goesBack_of Z layF m hp _ (fun _ _ h => restLike_cleared h) base In hF

/-- **At a step that leaves the verifier's state** (the chain's front; "laid"). -/
theorem carry_goesBack_same {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s)
    (base : Nat) (In : P × S → Strs → Prop)
    (hF : ∀ p s y, In (p, s) y → CarryFence Z m base (rest s)) :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) :=
  carry_goesBack_of Z layF m hp rel (fun s t h => by rw [hrel s t h]; exact RestLike.refl s) base
    In hF

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.firstFront_like
#print axioms Johnson.Desc.First.Walk.Tied.carryRow_like
#print axioms Johnson.Desc.First.Walk.Tied.rest_cleared
#print axioms Johnson.Desc.First.Walk.Tied.carry_back_of
#print axioms Johnson.Desc.First.Walk.Tied.restLike_cleared
#print axioms Johnson.Desc.First.Walk.Tied.restLike_shut
#print axioms Johnson.Desc.First.Walk.Tied.carry_back_cleared
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_of
#print axioms Johnson.Desc.First.Walk.Tied.longFront_stays
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_cleared
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_same
