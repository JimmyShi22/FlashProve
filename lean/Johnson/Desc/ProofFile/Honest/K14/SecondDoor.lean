-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondDoor.lean: kind K14: "K14, second part" (⟨3, none, 0,
.K14⟩): WHAT THE LAST CHAIN's OWN START ALREADY GIVES, AND WHAT IS LEFT IN THE LIST. The member is
the chain's first: the state in front of it is what the start (Johnson/Desc/Third/State.lean:
start₃E) has returned of the two earlier chains' last states. Of the twenty-four tests of secondOwed
(Honest/K14/SecondOwed.lean) thirteen follow from that: eleven are left. A definition with code, and
statements with their proofs.

  start_gives     what a state that start₃E returns is: the two ends are at hand; the shape is
                  lawful at the codes (linOk) and does not split the row (Dot); no root is received,
                  and the first own tree's number counts one tree more; the statement, the book and
                  the numbers of W and of the own group are the first chain's; both ends' codes are
                  the plan's; the own group is there, in no test, with W's code
  omega_lawful    what linOk says of Omega's shape: no mask rows; main rows; degree 3; an answer;
                  its code's number is in the table
  trees_one       one notice with main rows of a degree that is not 0, and without mask rows, makes
                  one tree
  secondDoor p s  **THE ELEVEN THAT ARE LEFT**
  noTwice_of_order one of the eleven, "join: no member twice", follows where the statement is in
                  order (Means.InOrder) and the own group is there: so at the letter order that
                  second_at_last (Honest/K14/SecondBehind.lean) lays it is in the thread's form
                  already
  has_self        a number below an array's size names an entry
  door_owed       **at a state that the start returns: all of secondDoor true: all of secondOwed
                  true**
  second_door     so the member's decide function returns
  begun_of_thr    where the thread holds in front of the member 0, the state is one that the letter
                  first allows
  second_acceptedS_door, second_accepted_door   **AcceptedS at every Said, and Accepted, at the
                  member 0, at every fall, general in the letters, UNDER THREE PREMISES**: hblk:
                  whatever stands at the number 0 of the letters' list declares no round and has
                  batchLinearConstraintsSecondPart p's decide function (LikeSecond, Honest/K14/SecondBehind.lean); hS: the
                  chain begins only at a state that start₃E returns; hD: under all that AcceptedS
                  itself hands out (for Accepted: wherever the thread holds in front of the member)
                  the eleven are true
  start_at_last   **hS at the library's own description**: by the library's start₃_ended and
                  start₃_fin (Johnson/ToldDescR/StartClean.lean)
  like_at_last    hblk at the library's own description
  second_acceptedS_last, second_accepted_last   **so both at the member 0 of lettersLast's own
                  thread** (Honest/Thread/LastHead.lean), whatever its free arguments are: hD alone
                  is left

GIVEN BY THE START: the two ends are at hand; the shape does not split the row (Dot); no root is
received yet; join: the group is there, no test has begun. GIVEN BY THE START WITH "Omega: it has
the plan's shape": join: the group's main code (W's code is Omega's where the shape does not split)
and the group's mask code (Omega has no mask rows); adopt: every notice's shape fits the codes,
counts an answer, the trees can be laid, a number and a source for each tree; elsewhere: the same
main code, the same mask code (both ends' codes are the plan's).

THE LIST BY ITSELF IS NO TEST OF THE MEMBER: it is meant at a state that the start returns. Where no
two ends are at hand it is EMPTY, so all true, and the member rejects. Four of the eleven say that
something is there and are listed only where they are false: seven are listed where all is there.
Where takeOver returns an error the last three are left out.

What is not claimed. That the eleven hold at any pair of ends: a file that is not part of this tree
evaluates them at a small synthetic pair; files above this one give them under premises of their own
(Honest/K14/SecondAll.lean: second_door_fold; Honest/K14/SecondAtRun.lean: second_door_run). No
theorem says that no further test of the eleven follows from the start: evaluations at one plan, in
that file outside this tree, are all that speaks for it. The converse of door_owed. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondOwed
import Johnson.Desc.Third.Law.AtDoor
import Johnson.ToldDescR.StartClean
import Johnson.Desc.Third.Law.Mask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW OracleNotice)
open Desc.Plain (DState)
open VerifiableInference.Desc (Block OpenedColumn Own.tensorInOrder Own.placeFits Own.allZero
  Own.sentShapeFits)
open VerifiableInference.Desc.Ground (Clauses ok has adoptL)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut FirstEnd₃ batchLinearConstraintsSecondPart takeOver plainArm
  firstStepB rootsB start₃ start₃E firstOutFrom numbersOk)
open VerifiableInference.Desc.Third.Law (numbersOk_inv)

/-- **What a state that the start returns is**: the two ends are at hand; linOk holds at the plan's
codes and shape, and the shape does not split the row (Dot); no root is received, and the first own
tree's number counts one tree more; the statement, the book and the numbers of W and of the own
group are the first chain's; both ends' codes are the plan's; the own group is there, in no test,
with W's code. -/
theorem start_gives (p : P₁₄) (h : FirstEnd₃) (o : SharedOut) (s : S₃)
    (hs : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s) :
    (∃ g, s.loc.border = some { g := g, shared := o }) ∧ OnBytes.linOk p.codes p.S = true ∧
      plainArm p.S = true ∧ firstStepB s.roots s.loc.firstTree s.book = true ∧ s.st = h.st ∧
      s.book = h.book ∧ s.loc.w = h.w ∧ s.loc.own = h.own ∧ s.st.codes = p.codes ∧
      o.st.codes = p.codes ∧
      ∃ G, s.st.groups[s.loc.own]? = some G ∧ G.inRun = false ∧ G.code = p.S.w.code := by
  have hlin := VerifiableInference.Desc.Third.Law.start₃E_lin _ _ _ _ _ _ _ _ _ _ _ hs
  unfold start₃E at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · rename_i f hf
      split at hs
      · cases hs
      · rename_i t ht
        obtain rfl : t = s := Except.ok.inj hs
        unfold firstOutFrom at hf
        split at hf
        · rename_i r
          split at hf
          · rename_i hc
            dsimp only at hf
            split at hf
            · rename_i hn
              obtain rfl := Option.some.inj hf
              rw [Bool.and_eq_true] at hc
              unfold start₃ at ht
              split at ht
              · rename_i hk
                obtain rfl := Option.some.inj ht
                simp only [Bool.and_eq_true] at hk
                obtain ⟨_, G, -, hG, -, -, hcode, -, hrun⟩ := numbersOk_inv _ _ hn
                refine ⟨⟨_, rfl⟩, hlin, hc.1, ?_, rfl, rfl, rfl, rfl, of_decide_eq_true hk.1.1,
                  of_decide_eq_true hk.1.2, G, hG, hrun, hcode⟩
                have hr : h.roots = h.book.trees.size := eq_of_beq hk.2
                show ((0 : Nat) == 0 && h.book.trees.size + 1 == h.roots + 1) = true
                rw [hr]
                simp
              · cases ht
            · cases hf
          · cases hf
        · cases hf

/-- What linOk says of Omega's shape. -/
theorem omega_lawful (codes : OnBytes.Codes) (S : OnBytes.Params.LinShape)
    (h : OnBytes.linOk codes S = true) :
    S.omega.maskRows = 0 ∧ S.omega.mainRows ≠ 0 ∧ S.omega.mainDeg = 3 ∧ 1 ≤ S.omega.answers ∧
      S.omega.code < codes.base.size := by
  unfold OnBytes.linOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hok, -⟩, hcode⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  unfold OnBytes.Params.LinShape.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hv⟩, -⟩, -⟩, -⟩, hm⟩, -⟩, -⟩, -⟩, -⟩ := hok
  unfold OnBytes.Params.LinShape.vectorMessageOk at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨-, v1⟩, v2⟩, v3⟩ := hv
  exact ⟨eq_of_beq hm, by simpa using v1, eq_of_beq v2, v3, hcode⟩

/-- One notice with main rows of a degree that is not 0 (h1, h2), and without mask rows (h0), makes
one tree. -/
theorem trees_one (codes : OnBytes.Codes) (n : OracleNotice) (h0 : n.shape.maskRows = 0)
    (h1 : n.shape.mainRows ≠ 0) (h2 : n.shape.mainDeg ≠ 0) :
    ∃ lay, VerifiableInference.Desc.Own.treesMade codes #[n] = some lay ∧ lay.shapes.size = 1 := by
  cases h : VerifiableInference.Desc.Own.treesMade codes #[n] with
  | none =>
    exfalso
    simp [VerifiableInference.Desc.Own.treesMade, VerifiableInference.Desc.Own.treeOf,
      VerifiableInference.Desc.Own.treeOfPass, VerifiableInference.Desc.Own.fillStep,
      VerifiableInference.Desc.Own.closeTrees, h0, h1, h2, List.range_succ,
      OnBytes.TreeShape.maskWidth, OnBytes.TreeShape.mainWidth] at h
  | some lay =>
    refine ⟨lay, rfl, ?_⟩
    simp [VerifiableInference.Desc.Own.treesMade, VerifiableInference.Desc.Own.treeOf,
      VerifiableInference.Desc.Own.treeOfPass, VerifiableInference.Desc.Own.fillStep,
      VerifiableInference.Desc.Own.closeTrees, h0, h1, h2, List.range_succ,
      OnBytes.TreeShape.maskWidth, OnBytes.TreeShape.mainWidth] at h
    rw [← h]
    simp

/-- **THE ELEVEN THAT ARE LEFT**, meant at a state that the start returns. Four say that something
is there and are listed only where they are false. Where no two ends are at hand the list is empty:
by itself it is no test of the member. Where takeOver returns an error the last three tests are left
out (the arm that gives the empty list). -/
def secondDoor (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => []
  | some x =>
  match x.shared.book.place[x.shared.omega]? with
  | none => [("Omega: it has a place in the shared chain's book", false)]
  | some q =>
  match x.shared.book.trees[q.1]? with
  | none => [("Omega: its tree is in the shared chain's book", false)]
  | some t =>
  match x.shared.st.oracles[x.shared.omega]? with
  | none => [("Omega: it is in the shared chain's statement", false)]
  | some y =>
    ("Omega: it has a tree to itself", t.parts.size == 1) ::
    ("Omega: it has the plan's shape", decide (y.shape = p.S.omega)) ::
    ("adopt: statement and book are in step", s.st.oracles.size == s.book.place.size) ::
    ("elsewhere: sampled there", y.sampled) ::
    ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size)) ::
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => [("the row (Dot) can be made", false)]
      | some dot =>
        [("addRow: the terms fit their places", has a.2.st.groups[s.loc.own]? fun G =>
            dot.terms.all fun t =>
              Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0),
         ("addRow: ON VALUES: no coefficient on a pad", has a.2.st.groups[s.loc.own]? fun G =>
            G.members.all fun o =>
              ((a.2.st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
                Own.allZero (dot.coefficient o q.1 q.2))]

/-- **"join: no member twice" where the statement is in order**: every member of a group is a
message that is there, so none bears the next free number. -/
theorem noTwice_of_order (s : S₃) (hI : OnBytes.Means.InOrder s.st) (G : OnBytes.Group)
    (hG : s.st.groups[s.loc.own]? = some G) :
    has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size) = true := by
  rw [hG]
  show (!G.members.contains s.st.oracles.size) = true
  cases hc : G.members.contains s.st.oracles.size with
  | false => rfl
  | true =>
    have hm : s.st.oracles.size ∈ G.members.toList := by
      simpa using hc
    exact absurd ((hI.groups _ G hG).there _ hm) (Nat.lt_irrefl _)

/-- A number below an array's size names an entry. -/
theorem has_self {α : Type} [BEq α] [LawfulBEq α] (xs : Array α) (i : Nat) (h : i < xs.size) :
    (has xs[i]? fun c => xs[i]? == some c) = true := by
  rw [Array.getElem?_eq_getElem h]
  simp [has]

/-- **At a state that the start returns: all of secondDoor true: all of secondOwed true.** -/
theorem door_owed (p : P₁₄) (h : FirstEnd₃) (o : SharedOut) (s : S₃)
    (hs : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s)
    (hD : ok (secondDoor p s) = true) : ok (secondOwed p s) = true := by
  obtain ⟨⟨g, hx⟩, hlin, h2, h3, -, -, -, -, hc, hco, G, hG, hrun, hcode⟩ :=
    start_gives p h o s hs
  obtain ⟨w0, w1, w2, w3, w4⟩ := omega_lawful _ _ hlin
  unfold secondDoor at hD
  unfold secondOwed
  rw [hx] at hD ⊢
  dsimp only at hD ⊢
  cases hq : o.book.place[o.omega]? with
  | none => rw [hq] at hD; cases hD
  | some q =>
    rw [hq] at hD
    dsimp only at hD ⊢
    cases ht : o.book.trees[q.1]? with
    | none => rw [ht] at hD; cases hD
    | some t =>
      rw [ht] at hD
      dsimp only at hD ⊢
      cases hy : o.st.oracles[o.omega]? with
      | none => rw [hy] at hD; cases hD
      | some y =>
        rw [hy] at hD
        dsimp only at hD ⊢
        rw [ok_cons, ok_cons, ok_cons, ok_cons, ok_cons] at hD
        simp only [Bool.and_eq_true] at hD
        obtain ⟨h6, h8, a3, e3, j7, hR⟩ := hD
        rw [ok_cons, ok_cons, ok_cons, ok_cons, ok_append, ok_cons, ok_cons, ok_cons, ok_cons,
          ok_cons, ok_cons, ok_cons, ok_cons]
        simp only [Bool.and_eq_true]
        have hsh : y.shape = p.S.omega := of_decide_eq_true h8
        have hA : ok (adoptL s.st s.book #[{ shape := y.shape, leafClass := p.S.omegaLeafClass }]
            #[(t.number, t.src)]) = true := by
          obtain ⟨lay, hl, hn⟩ := trees_one s.st.codes
            { shape := y.shape, leafClass := p.S.omegaLeafClass } (by rw [hsh]; exact w0)
            (by rw [hsh]; exact w1) (by rw [hsh, w2]; decide)
          simp only [ok, adoptL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          refine ⟨?_, ?_, a3, ?_, ?_⟩
          · have : Own.sentShapeFits s.st.codes y.shape = true := by
              unfold Own.sentShapeFits
              rw [hsh, hc, w0, w2]
              simp [w4, Nat.pos_of_ne_zero w1]
            simpa using this
          · have : (y.shape.answers != 0) = true := by
              rw [hsh]
              simpa using Nat.ne_of_gt w3
            simpa using this
          · unfold VerifiableInference.Desc.Own.treesCan
            rw [hl]
            rfl
          · rw [hl]
            show (lay.shapes.size == 1) = true
            rw [hn]
            rfl
        refine ⟨h2, h3, h6, h8, hA, e3, ?_, ?_, ?_, ?_, ?_, ?_, j7, hR⟩
        · rw [Bool.or_eq_true]
          refine Or.inr ?_
          rw [hco, ← hc]
          exact has_self _ _ (by rw [hsh, hc]; exact w4)
        · rw [Bool.or_eq_true]
          refine Or.inl ?_
          rw [hsh, w0]
          rfl
        · rw [hG]
          rfl
        · rw [hG]
          show (!G.inRun) = true
          rw [hrun]
          rfl
        · rw [hG]
          show (y.shape.mainRows == 0 || y.shape.code == G.code) = true
          have hp : p.S.w.code = p.S.omega.code := by
            have := h2
            unfold plainArm OnBytes.Params.LinShape.ownSplitNeeded at this
            simpa using this
          rw [hcode, hp, hsh]
          simp
        · rw [hG]
          show (y.shape.maskRows == 0 || y.shape.maskCode == G.maskCode) = true
          rw [hsh, w0]
          rfl

/-- So the member's decide function returns. -/
theorem second_door {Cl : Type} (p : P₁₄) (h : FirstEnd₃) (o : SharedOut) (s : S₃)
    (hs : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s)
    (hD : ok (secondDoor p s) = true) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s' :=
  second_owed p s rs gs (door_owed p h o s hs hD)

/-! ## Accepted -/

section accepted
variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Xi Tr X P₁ Wt : Type}
  (L : LastThread.Letters Bk S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt) (p : P₁₄)

/-- Where the thread holds in front of the member 0, the state is one that the letter first allows,
AT SOME a: WHICH a IS NOT SAID: it is tied neither to the coins nor to the stand. (begun_is_ends,
Honest/K14/BegunIsEnds.lean, names it.) -/
theorem begun_of_thr {k : Coins Bk} {s : S₃} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hA : Thr L.thread 0 k s m E) : ∃ a, L.first a s := by
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  have e : s₀ = s := by
    have h' : (Except.ok (s₀, _, c₀) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) =
        .ok (s, [], []) := hfold
    exact congrArg Prod.fst (Except.ok.inj h')
  subst e
  exact ⟨_, hbeg⟩

/-- **AcceptedS at the member 0, at every Said and every fall, general in the letters, under three
premises.** hblk: whatever stands at the number 0 of the letters' list is LikeSecond: it declares no
round and has batchLinearConstraintsSecondPart p's decide function. hS: the chain begins only at a state that start₃E
returns. hD: under all that AcceptedS itself hands out the eleven are true. -/
theorem second_acceptedS_door (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hS : ∀ a s₀, L.first a s₀ → ∃ (h : FirstEnd₃) (o : SharedOut),
      start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s₀)
    (hD : ∀ blk, L.bs[0]? = some blk → ∀ k s m E ds y cols, ThrS L.thread Said 0 k s m E →
      drawsFit blk.rounds ds = true →
      chainStopAt (L.thread.φ.sees m.st.input) [blk] L.thread.hs m.loc ds = none →
      fall 0 s ds = none → L.thread.Moved blk k m E ds y cols → ok (secondDoor p s) = true) :
    AcceptedS L.thread Said fall 0 :=
  second_acceptedS L p Said fall hblk (fun blk hb k s m E ds y cols hA hd hst hfl hMv => by
    obtain ⟨a, ha⟩ := begun_of_thr L hA.1
    obtain ⟨h, o, hs⟩ := hS a s ha
    exact owed_list p s (door_owed p h o s hs (hD blk hb k s m E ds y cols hA hd hst hfl hMv)))

/-- **Accepted at the member 0, at every fall, general in the letters, under hblk, hS and hD**:
second_acceptedS_door where nothing is said, with less handed to hD. -/
theorem second_accepted_door (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hS : ∀ a s₀, L.first a s₀ → ∃ (h : FirstEnd₃) (o : SharedOut),
      start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s₀)
    (hD : ∀ k s m E, Thr L.thread 0 k s m E → ok (secondDoor p s) = true)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) : Accepted L.thread fall 0 :=
  fun blk hb k s m E ds y cols hA =>
    second_acceptedS_door L p (fun _ _ _ => True) fall hblk hS
      (fun _ _ k s m E _ _ _ h _ _ _ _ => hD k s m E h.1) blk hb k s m E ds y cols ⟨hA, trivial⟩

end accepted

/-- **hS at the library's own description**: where its start of the last chain returns a state, the
first chain stands at its end, the shared chain has ended, the first chain's last state names W, and
the state is what start₃E returns of the two: by the library's start₃_fin and start₃_ended
(Johnson/ToldDescR/StartClean.lean). -/
theorem start_at_last (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) (x : ProofFile.InstPub) (s₁ : P5J.TS)
    (s₂ : Desc.K14.St) (s₀ : S₃)
    (h : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s₀) :
    ∃ (f : FirstEnd₃) (e : OnBytes.Proof.SharedEnd), s₁.fin = true ∧
      VerifiableInference.Desc.Third.firstOfS s₁ = some f ∧ Desc.K14.ended s₂ = some e ∧
      start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w f.own f.mask
        f.pending (VerifiableInference.Desc.Third.sharedOfEnd e) = .ok s₀ := by
  have hfin := ToldDesc.start₃_fin OnBytes.secondHashFunction ProofFile.pureRoad.links Zp
    (Desc.K14.Law.seatN Zp Np) (P2Third.secondSeatOf Zp Np) (fun s => s) (ProofFile.startS Zp) cF x s₁ s₂
    s₀ h
  obtain ⟨e, he, hs⟩ := ToldDesc.start₃_ended OnBytes.secondHashFunction ProofFile.pureRoad.links Zp
    (Desc.K14.Law.seatN Zp Np) (P2Third.secondSeatOf Zp Np) (fun s => s) (ProofFile.startS Zp) cF x s₁ s₂
    s₀ h
  have hs' : (match VerifiableInference.Desc.Third.firstOfS s₁ with
    | none => (.error "the first chain's end names no W" : Except String S₃)
    | some f => start₃E (ToldDesc.p14At Zp).codes (ToldDesc.p14At Zp).S f.st f.book f.roots f.w
        f.own f.mask f.pending (VerifiableInference.Desc.Third.sharedOfEnd e)) = .ok s₀ := hs
  cases hf : VerifiableInference.Desc.Third.firstOfS s₁ with
  | none => rw [hf] at hs'; cases hs'
  | some f =>
    rw [hf] at hs'
    exact ⟨f, e, hfin, rfl, he, hs'⟩

section atLast
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL)
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : MeaningL S₃ Wt) (PL : PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → Nat) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The member at 0 of the library's own description's last chain is like batchLinearConstraintsSecondPart. -/
theorem like_at_last (blk : Block S₃ ProofFile.Cl)
    (hb : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder[0]? = some blk) :
    LikeSecond blk (ToldDesc.p14At Zp) := by
  obtain rfl := Option.some.inj ((first_of_last Zp Np cF).symm.trans hb)
  exact ⟨rfl, rfl⟩

/-- **AcceptedS at the member 0 of the last chain's letters at the library's description, at every
Said and every fall, whatever the free arguments of lettersLast are**: ONE PREMISE: under all that
AcceptedS itself hands out the eleven are true. -/
theorem second_acceptedS_last
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String)
    (hD : ∀ blk, (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item
        n₁ n₂ Vd Rd Kp w).bs[0]? = some blk → ∀ k s m E ds y cols,
      ThrS (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂
        Vd Rd Kp w).thread Said 0 k s m E → drawsFit blk.rounds ds = true →
      chainStopAt ((LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed
        item n₁ n₂ Vd Rd Kp w).thread.φ.sees m.st.input) [blk] (LastThread.lettersLast Zp Np cF H N
        Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp w).thread.hs m.loc ds = none →
      fall 0 s ds = none →
      (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd
        Rd Kp w).thread.Moved blk k m E ds y cols →
      ok (secondDoor (ToldDesc.p14At Zp) s) = true) :
    AcceptedS (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item
      n₁ n₂ Vd Rd Kp w).thread Said fall 0 := by
  refine second_acceptedS_door _ (ToldDesc.p14At Zp) Said fall (like_at_last Zp Np cF) ?_ hD
  intro a s₀ ha
  obtain ⟨f, e, -, -, -, hs⟩ := start_at_last Zp Np cF a.1.1 a.1.2 a.2 s₀ ha
  exact ⟨f, _, hs⟩

/-- **Accepted there**: second_acceptedS_last where nothing is said, with less handed to hD. -/
theorem second_accepted_last
    (hD : ∀ k s m E, Thr (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table
      fixed item n₁ n₂ Vd Rd Kp w).thread 0 k s m E →
      ok (secondDoor (ToldDesc.p14At Zp) s) = true)
    (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    Accepted (LastThread.lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item
      n₁ n₂ Vd Rd Kp w).thread fall 0 :=
  fun blk hb k s m E ds y cols hA =>
    second_acceptedS_last Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd
      Kp w (fun _ _ _ => True) fall (fun _ _ k s m E _ _ _ h _ _ _ _ => hD k s m E h.1) blk hb k s
      m E ds y cols ⟨hA, trivial⟩

end atLast

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.noTwice_of_order
#print axioms ProofFile.Honest.K14.omega_lawful
#print axioms ProofFile.Honest.K14.trees_one
#print axioms ProofFile.Honest.K14.second_acceptedS_door
#print axioms ProofFile.Honest.K14.like_at_last
#print axioms ProofFile.Honest.K14.second_acceptedS_last
#print axioms ProofFile.Honest.K14.second_accepted_last
#print axioms ProofFile.Honest.K14.begun_of_thr
#print axioms ProofFile.Honest.K14.second_accepted_door
#print axioms ProofFile.Honest.K14.start_at_last
#print axioms ProofFile.Honest.K14.start_gives
#print axioms ProofFile.Honest.K14.has_self
#print axioms ProofFile.Honest.K14.door_owed
#print axioms ProofFile.Honest.K14.second_door
