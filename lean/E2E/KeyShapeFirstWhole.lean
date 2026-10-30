-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstWhole.lean: THE LETTERS OF THE CUT STRUCTURE | VALUES
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) FOR THE KEY FILE's FIRST CHAIN, WITH CODE AT EVERY
SUB-PROTOCOL; AND (B1) AT EVERY NUMBER OF THE DESCRIPTION's OWN FLAT LIST, with no premise at a
sub-protocol. Definitions, statements and proofs. Sub-protocols of the verifier's: NOTHING IS SHOWN
OF ANY PROVER.

How. Two lists side by side: the chain's flat list and a list of guards on the shape. `CarriesB`
says (B1) of one sub-protocol and one guard; where it holds of the two lists member by member
(`List.Forall₂`), (B1) holds at every number of the shape whose guard at b is the list's b-th
(`ZL`, `carries_list`). So no number of a place in the list is ever computed.

  `CarriesB`, `carriesB_exact`, `carriesB_fit`, `carriesB_any`, `carriesB_bare`: (B1) of one
    sub-protocol and one guard; from E2E/KeyShapeLink.lean's `ExactAt`; from (B1r) at rounds that
    fit; from (B1r) at all rounds; at the sub-protocol as the flat list lays it.
  `ZL`, **`carries_list`**: the shape of a list of guards, and the rule.
  `pairs_flatMap`, `pairs_of_get`: the relation over joined lists; from the lists' members by
    number.
  `look_at`: a lookup in the numbered list is the lookup of its number.
  **`gAll₁`**: the first chain's guards, in the order of its flat list.
  **`Z₁W`**: the letters. **`pairs₁`**: member by member. **`carries_whole₁`**: (B1) at every
    number.
  `ReturnsQ`, `returnsQ_exact`, `returnsQ_rounds`, `returns_get`, `returns_list`, `quiet₁`,
    **`returns_whole₁`**: (B2) AT EVERY SUB-PROTOCOL THAT HAS NO ROUND, with no test on values: the
    links' five each and "rng.0.rows". The seal has one round: of it this law says nothing; its (B2)
    is E2E/KeyShapeFirstBack.lean's `seal_both`.
  `pubOf`, **`flat₁_tie`**, **`start₁_shape`**: at the key file's description: its first chain's
    flat list is this file's; the shape of the state at which it starts the chain is
    E2E/KeyShapeFirstFront.lean's `a₀`.

Limits.
- Three premises on public values: "w.1.send" is there; the two conditions on the ranges' test's
  place (`ranges_place` pays them from that sub-protocol's own test on public values).
- `returns_whole₁` has one premise more on public values: the ranges' test has a round.
- (B2) at the sub-protocols with rounds is not assembled here: E2E/KeyShapeFirstReturns.lean does
  it; at the ranges' test: E2E/KeyRangesReturns.lean.


-/
import E2E.KeyShapeFirstBack
import E2E.KeyShapeLink

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (Shape Carries CarriesR)
open VerifiableInference.Desc (Block roundsFit noDigest step_iff)
open VerifiableInference.Desc.Key (FirstState Claim lookupsOf lookupLink layRows rangesParams
  groupsTold rootsBefore rootsAt pieces)
open AtPublicFiles.KeyShape (Pub1 ExactAt gLink link_exact layRows_exactAt gLayRows lookAt)

/-! ## One sub-protocol and one guard -/

section One
variable {S Cl Sh : Type} {ft : Nat} {sh : S → Sh} {blk : Block S Cl}
  {g : Sh → Except String Sh}

/-- **(B1) of one sub-protocol and one guard.** -/
def CarriesB (ft : Nat) (sh : S → Sh) (blk : Block S Cl) (g : Sh → Except String Sh) : Prop :=
  ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) → g (sh s) = .ok t → t = sh s'

theorem carriesB_exact (h : ExactAt ft sh blk g) : CarriesB ft sh blk g := by
  intro s rs cols s' n t hs hg
  obtain ⟨hfit, hdec, -⟩ := (step_iff ft blk s s' rs cols n).1 hs
  obtain ⟨s'', e, r⟩ := h s t rs cols hg hfit
  rw [hdec] at e
  obtain rfl := Except.ok.inj e
  exact r.symm

theorem carriesB_fit (h : ∀ rs gs, roundsFit blk.rounds rs = true →
    CarriesR sh (fun s => blk.decide s (rs.map noDigest) gs) g) : CarriesB ft sh blk g := by
  intro s rs cols s' n t hs hg
  obtain ⟨hfit, hdec, -⟩ := (step_iff ft blk s s' rs cols n).1 hs
  exact h rs _ hfit.1 s s' t hdec hg

theorem carriesB_any (h : ∀ rs gs, CarriesR sh (fun s => blk.decide s rs gs) g) :
    CarriesB ft sh blk g := carriesB_fit fun rs gs _ => h (rs.map noDigest) gs

theorem carriesB_bare (h : CarriesB ft sh blk g) : CarriesB ft sh blk.asBare g := h

/-- The shape whose guard at b is a list's b-th. -/
def ZL (sh : S → Sh) (gs : List (Sh → Except String Sh))
    (v : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape S where
  Sh := Sh
  sh := sh
  g := fun b => (gs[b]?).getD fun _ => .error "the chain has no such sub-protocol"
  vals := v

/-- **The rule**: member by member, so at every number. -/
theorem carries_list (v : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    ∀ (bs : List (Block S Cl)) (gs : List (Sh → Except String Sh)),
      List.Forall₂ (CarriesB ft sh) bs gs → ∀ j, Carries bs ft (ZL sh gs v) j
  | _, _, .nil, _ => fun _ hb => by cases hb
  | _, _, .cons (a := b) (b := g) (l₁ := bs) (l₂ := gs) h _, 0 => fun blk hb => by
    obtain rfl : b = blk := Option.some.inj hb
    exact h
  | _, _, .cons (a := b) (b := g) (l₁ := bs) (l₂ := gs) _ ht, j + 1 => fun blk hb =>
    carries_list v bs gs ht j blk hb

theorem pairs_flatMap {α β γ : Type} {R : β → γ → Prop} (f : α → List β) (k : α → List γ) :
    ∀ l : List α, (∀ x ∈ l, List.Forall₂ R (f x) (k x)) →
      List.Forall₂ R (l.flatMap f) (l.flatMap k)
  | [], _ => .nil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a (List.mem_cons_self ..))
      (pairs_flatMap f k l fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem pairs_of_get {β γ : Type} {R : β → γ → Prop} : ∀ (l : List β) (m : List γ),
    l.length = m.length → (∀ (i : Nat) b c, l[i]? = some b → m[i]? = some c → R b c) →
      List.Forall₂ R l m
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | b :: l, c :: m, h, hr =>
    .cons (hr 0 b c rfl rfl) (pairs_of_get l m (Nat.succ.inj h) fun i => hr (i + 1))

end One

/-! ## The first chain -/

variable (Q : Pub1) (cs : Codes) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (N : H2U.PlaceNums)

/-- A lookup in the numbered list is the lookup of its number. -/
theorem look_at {x} (hx : x ∈ (lookupsOf Q.one).zipIdx) : x.1 = lookAt Q.one x.2 := by
  have h := List.mem_zipIdx_iff_getElem?.1 hx
  unfold lookAt
  rw [List.getD_eq_getElem?_getD, h]
  rfl

/-- **The first chain's guards on the shape**, in the order of its flat list. -/
def gAll₁ : List (Sh₁B → Except String Sh₁B) :=
  gIdx Q pieces (groupsTold told 0 (rootsAt D 0)) ::
    [gMsg Q pieces (groupsTold told (rootsBefore D 2) (rootsAt D 2))] ++
    ((lookupsOf Q.one).zipIdx.flatMap fun x => gLink Q x.2) ++
    [gLayRows Q, gRng Q N, gBatt Q cs pieces (sentAt D), gSendW Q pieces (groupsW D told)] ++
    [gSealB]

/-- **The letters of the cut for the first chain, with code at every sub-protocol.** v: the named
tests on values. -/
def Z₁W (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    Shape FirstState := ZL (sh₁B Q cs) (gAll₁ Q cs D told N) v

/-- **The flat list, written out.** -/
theorem flat₁_whole (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw) :
    flat₁ Q D told N =
    (VerifiableInference.Desc.Key.sendIndexMasks Q.one pieces
        (groupsTold told 0 (rootsAt D 0))).asBare ::
      [(VerifiableInference.Desc.Key.sendOwnMessage Q.one pieces
        (groupsTold told (rootsBefore D 2) (rootsAt D 2))).asBare] ++
      ((lookupsOf Q.one).zipIdx.flatMap fun x =>
        (lookupLink Q.one Q.set x.2 x.1).blocksInOrder) ++
      [(layRows Q.one).asBare, H2K.JointK.rngEntry Q.one N,
        (VerifiableInference.Desc.Key.batchTableRows keysAt Q.one pieces (sentAt D)).asBare,
        bw.asBare] ++
      [(VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).last.asBare] := by
  rw [flat₁_cut Q D told N bw hw]
  unfold H2K.JointK.keyFirstPre
  show _ :: ([_] ++ ((lookupsOf Q.one).zipIdx.map fun x =>
    lookupLink Q.one Q.set x.2 x.1).flatMap VerifiableInference.Desc.Link.blocksInOrder ++ [_]) ++ _ = _
  rw [List.flatMap_map]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rfl

/-- **Member by member.** -/
theorem pairs₁ (ft : Nat) (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (he : (rangesParams N).early = true) (ha : (rangesParams N).answers = 1) :
    List.Forall₂ (CarriesB ft (sh₁B Q cs)) (flat₁ Q D told N) (gAll₁ Q cs D told N) := by
  rw [flat₁_whole Q D told N bw hw]
  unfold gAll₁
  refine List.rel_append (List.rel_append (List.rel_append (.cons ?_ (.cons ?_ .nil)) ?_)
    (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))) (.cons ?_ .nil)
  · exact carriesB_bare (carriesB_fit fun rs gs hf => idx_carries Q _ pieces _ rs gs hf)
  · exact carriesB_bare (carriesB_fit fun rs gs hf => msg_carries Q _ pieces _ rs gs hf)
  · refine pairs_flatMap _ _ _ fun x hx => ?_
    rw [look_at Q hx]
    exact pairs_of_get _ _ rfl fun k blk g hb hg =>
      carriesB_exact (link_exact Q _ x.2 ft k blk g hb hg)
  · exact carriesB_bare (carriesB_exact (layRows_exactAt Q _ ft))
  · exact carriesB_bare (carriesB_any fun rs gs => rng_carries Q cs N he ha rs gs)
  · exact carriesB_bare (carriesB_any fun rs gs => batt_carries Q cs _ _ rs gs)
  · exact carriesB_bare (carriesB_fit fun rs gs hf => sendW_carries Q cs _ _ _ bw hw rs gs hf)
  · exact carriesB_bare (carriesB_any fun rs gs =>
      (seal_both (Cl := Claim) Q cs pieces [] rs gs).1)

/-- **(B1) AT EVERY NUMBER OF THE FIRST CHAIN's OWN FLAT LIST.** -/
theorem carries_whole₁ (ft : Nat)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (he : (rangesParams N).early = true) (ha : (rangesParams N).answers = 1) (j : Nat) :
    Carries (flat₁ Q D told N) ft (Z₁W Q cs D told N v) j :=
  carries_list v _ _ (pairs₁ Q cs D told N ft bw hw he ha) j

/-! ## (B2) at the sub-protocols without a round -/

section Quiet
open ProofFile.Honest (Returns)

/-- **(B2) of one sub-protocol without a round and one guard**: with no test on values. Of a
sub-protocol that has a round it says nothing. -/
def ReturnsQ {S Cl Sh : Type} (ft : Nat) (sh : S → Sh) (blk : Block S Cl)
    (g : Sh → Except String Sh) : Prop :=
  blk.rounds = [] → ∀ s rs cols t, g (sh s) = .ok t → blk.Fits ft rs cols →
    ∃ s', blk.decide s (rs.map noDigest) (blk.shown ft rs cols) = .ok s'

theorem returnsQ_exact {S Cl Sh : Type} {ft : Nat} {sh : S → Sh} {blk : Block S Cl}
    {g : Sh → Except String Sh} (h : ExactAt ft sh blk g) : ReturnsQ ft sh blk g :=
  fun _ s rs cols t hg hf => by
    obtain ⟨s', e, -⟩ := h s t rs cols hg hf
    exact ⟨s', e⟩

theorem returnsQ_rounds {S Cl Sh : Type} {ft : Nat} {sh : S → Sh} {blk : Block S Cl}
    {g : Sh → Except String Sh} (h : blk.rounds ≠ []) : ReturnsQ ft sh blk g :=
  fun hr => absurd hr h

theorem returns_get {S Cl Sh : Type} {ft : Nat} {sh : S → Sh} :
    ∀ (bs : List (Block S Cl)) (gs : List (Sh → Except String Sh)),
      List.Forall₂ (ReturnsQ ft sh) bs gs → ∀ (j : Nat) (blk : Block S Cl), bs[j]? = some blk →
        ReturnsQ ft sh blk ((gs[j]?).getD fun _ => .error "the chain has no such sub-protocol")
  | _, _, .nil, _, _, hb => by cases hb
  | _, _, .cons (a := b) (b := g) (l₁ := bs) (l₂ := gs) h _, 0, blk, hb => by
    obtain rfl : b = blk := Option.some.inj hb
    exact h
  | _, _, .cons (a := b) (b := g) (l₁ := bs) (l₂ := gs) _ ht, j + 1, blk, hb =>
    returns_get bs gs ht j blk hb

/-- **The rule**: member by member, so at every number whose sub-protocol has no round. -/
theorem returns_list {S Cl Sh : Type} {ft : Nat} {sh : S → Sh}
    (v : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (bs : List (Block S Cl)) (gs : List (Sh → Except String Sh))
    (h : List.Forall₂ (ReturnsQ ft sh) bs gs) (j : Nat) (blk : Block S Cl)
    (hb : bs[j]? = some blk) (hr : blk.rounds = []) : Returns bs ft (ZL sh gs v) j := by
  intro blk' hb' s rs cols t hg hf _
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  exact returns_get bs gs h j blk hb hr s rs cols t hg hf

/-- **Member by member.** hR: the ranges' test has a round. -/
theorem quiet₁ (ft : Nat) (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hR : (H2K.JointK.rngEntry Q.one N).rounds ≠ []) :
    List.Forall₂ (ReturnsQ ft (sh₁B Q cs)) (flat₁ Q D told N) (gAll₁ Q cs D told N) := by
  rw [flat₁_whole Q D told N bw hw]
  unfold gAll₁
  refine List.rel_append (List.rel_append (List.rel_append (.cons ?_ (.cons ?_ .nil)) ?_)
    (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))) (.cons ?_ .nil)
  · exact returnsQ_rounds (by intro h; cases h)
  · exact returnsQ_rounds (by intro h; cases h)
  · refine pairs_flatMap _ _ _ fun x hx => ?_
    rw [look_at Q hx]
    exact pairs_of_get _ _ rfl fun k blk g hb hg =>
      returnsQ_exact (link_exact Q _ x.2 ft k blk g hb hg)
  · exact returnsQ_exact (layRows_exactAt Q _ ft)
  · exact returnsQ_rounds hR
  · exact returnsQ_rounds (by intro h; cases h)
  · refine returnsQ_rounds ?_
    unfold sendWAt VerifiableInference.Desc.Key.sendW at hw
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
    intro h
    cases h
  · intro _ s rs cols t hg _
    exact (seal_both (Cl := Claim) Q cs pieces [] (rs.map noDigest)
      (Block.shown ft (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).last.asBare rs
        cols)).2 s t hg rfl

/-- **(B2) AT EVERY SUB-PROTOCOL OF THE FIRST CHAIN THAT HAS NO ROUND**: whatever the named tests on
values are. -/
theorem returns_whole₁ (ft : Nat)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw)
    (hR : (H2K.JointK.rngEntry Q.one N).rounds ≠ []) (b : Nat) (blk : Block FirstState Claim)
    (hb : (flat₁ Q D told N)[b]? = some blk) (hr : blk.rounds = []) :
    Returns (flat₁ Q D told N) ft (Z₁W Q cs D told N v) b :=
  returns_list v _ _ (quiet₁ Q cs D told N ft bw hw hR) b blk hb hr

end Quiet

/-! ## At the key file's description -/

section Tie
variable (X : VerifiableInference.Desc.Key.Source) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The public values at which the first chain's shape is read, off the description's source. -/
abbrev pubOf : Pub1 := ⟨X.Y.k.oneTime, X.set⟩

/-- **The description's first chain's flat list is the list of this file.** -/
theorem flat₁_tie : (keyFileDescription X N P).first.blocksInOrder = flat₁ (pubOf X) X.Y.D.1 X.Y.told.1 N := rfl

/-- **The shape of the state at which the description starts the first chain**, whatever the
instance. -/
theorem start₁_shape (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (x : (keyFileDescription X N P).XiPub) :
    (Z₁W (pubOf X) cs X.Y.D.1 X.Y.told.1 N v).sh ((keyFileDescription X N P).start₁ x) =
      a₀ X.Y.k.oneTime.codes (backOf X.Y.k.oneTime.lin cs ([], #[], #[], none)) :=
  start_shape (pubOf X) _ X.Y.k.oneTime.codes

end Tie

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.carriesB_exact
#print axioms AtPublicFiles.AtFiles.carriesB_fit
#print axioms AtPublicFiles.AtFiles.carriesB_any
#print axioms AtPublicFiles.AtFiles.carriesB_bare
#print axioms AtPublicFiles.AtFiles.carries_list
#print axioms AtPublicFiles.AtFiles.pairs_flatMap
#print axioms AtPublicFiles.AtFiles.pairs_of_get
#print axioms AtPublicFiles.AtFiles.look_at
#print axioms AtPublicFiles.AtFiles.flat₁_whole
#print axioms AtPublicFiles.AtFiles.pairs₁
#print axioms AtPublicFiles.AtFiles.carries_whole₁
#print axioms AtPublicFiles.AtFiles.returnsQ_exact
#print axioms AtPublicFiles.AtFiles.returnsQ_rounds
#print axioms AtPublicFiles.AtFiles.returns_get
#print axioms AtPublicFiles.AtFiles.returns_list
#print axioms AtPublicFiles.AtFiles.quiet₁
#print axioms AtPublicFiles.AtFiles.returns_whole₁
#print axioms AtPublicFiles.AtFiles.flat₁_tie
#print axioms AtPublicFiles.AtFiles.start₁_shape
