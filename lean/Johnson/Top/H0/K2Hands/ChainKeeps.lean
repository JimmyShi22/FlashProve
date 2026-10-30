-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/ChainKeeps.lean: Johnson/Desc/FoldKeeps.lean's rule ONCE MORE, FOR A PROPERTY
WHOSE KEEPING BY A BLOCK MAY LEAN ON THE ROUNDS. A law file; no running text imports it.

THE RULE IS FoldKeeps.lean's, not this file's: what every part of a chain keeps (each block's
decision; each run of claims and each run behind the batching of a link's hearing blocks; a link's
laying, batching, closing and clearing) is kept by the fold over the chain's flat list. There it is
said of a reflexive and transitive relation on the verifier's state, and through `ofInv` of a
property; its `Decides` asks a block's law at ALL rounds. WHY ONCE MORE: a law may hold only on
rounds with a property R that the fold's own tests give (for one: the drawn elements are in
canonical form). Such a block has no `Decides`, so neither `Whole` nor `LinkKeeps` of that file can
be met where it stands among a link's hearing blocks.

  `KeepsD R P b`   a yes of the block's decision, on rounds that all have R, keeps P. `KeepsD.mono`.
  `KeepsRuns P b`  each of the block's runs of claims, and each of its runs behind the batching,
                   does.
  `keepsD_of_decides`, `keepsD_of_rel`, `keepsRuns_of_whole`, `linkKeeps_of`, `chainKeeps_of`
                   THE BRIDGES: whatever is paid in FoldKeeps.lean's form pays this one.
  `claimsInBy_keeps`, `afterIn_keeps`   of `claimsInBy` and `afterIn` over blocks with `KeepsRuns`.
  `LinkKeeps R P L`, `link_flat_keeps`     six clauses on a link; then every block of `L.blocksInOrder` has
                   `KeepsD`.
  `ChainKeeps R P c`, `chain_flat_keeps`   five clauses on a chain; the like for `c.blocksInOrder`.
  `step_keeps`, `fold_keeps`, `chainAt_keeps`   of `Block.step`, `foldBlocks`, `chainAt`: where all
                   rounds of the view have R, and R does not read the sealed digest.
  `keepsD_quiet`, `_andThen`, `_guarded`, `_retype`, `_inside`, `_under`   how `KeepsD` passes
                   through the ways in which a supplied block is made of a kind's block.
  `keepsRuns_bare`, `_guarded`   the like for `KeepsRuns`.
See also: Johnson/Desc/LinkLaw2.lean's `LinkSem.AfterKeeps` | `afterIn_keeps`: the like for the runs
behind the batching, at a link's typed meaning. Johnson/Desc/GroundKeeps.lean | CoreKeeps.lean:
relations that all the ground's plain functions keep.
Limits. Nothing on any one property or kind. Nothing on soundness or on hiding.

-/
import Johnson.Desc.SeatGuard
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc

variable {S Cl : Type} (R : Fmt.RoundView → Prop) (P : S → Prop)

/-- A yes of the block's decision, on rounds that all have R, keeps P. -/
def KeepsD (b : Block S Cl) : Prop :=
  ∀ s s' rs gs, (∀ r ∈ rs, R r) → b.decide s rs gs = .ok s' → P s → P s'

/-- Each run of claims and each run behind the batching keeps P. -/
def KeepsRuns (b : Block S Cl) : Prop :=
  (∀ c ∈ b.claims, ∀ n s y, c.2 n s = .ok y → P s → P y.2) ∧
    ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → P s → P s'

variable {R P}

/-- What is shown on all rounds holds on fewer. -/
theorem KeepsD.mono {R' : Fmt.RoundView → Prop} {b : Block S Cl} (h : KeepsD R P b)
    (hR : ∀ r, R' r → R r) : KeepsD R' P b :=
  fun s s' rs gs hr hy hs => h s s' rs gs (fun r hm => hR r (hr r hm)) hy hs

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem named_ok {α : Type} {n : String} {o : Option α} {x : α} (h : named n o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => exact congrArg some (Except.ok.inj h)

theorem lookup_mem {α : Type} {n : String} : ∀ {l : List (String × α)} {r : α},
    l.lookup n = some r → (n, r) ∈ l
  | [], _, h => by cases h
  | (m, a) :: t, r, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i e
      obtain rfl := Option.some.inj h
      rw [eq_of_beq e]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-! ## The bridges from FoldKeeps.lean's form -/

theorem keepsD_of_decides {b : Block S Cl} (h : Keeps.Decides (Keeps.ofInv P) b) : KeepsD R P b :=
  fun s s' rs gs _ hy hs => h s rs gs s' hy hs

/-- From a relation that carries P. -/
theorem keepsD_of_rel {Rel : S → S → Prop} (hc : ∀ s s', Rel s s' → P s → P s') {b : Block S Cl}
    (h : Keeps.Decides Rel b) : KeepsD R P b :=
  fun s s' rs gs _ hy hs => hc s s' (h s rs gs s' hy) hs

theorem keepsRuns_of_whole {b : Block S Cl} (h : Keeps.Whole (Keeps.ofInv P) b) : KeepsRuns P b :=
  ⟨fun c hc n s y hy hs => h.2.1 c hc n s y hy hs, fun c hc s s' hy hs => h.2.2 c hc s s' hy hs⟩

/-! ## The runs -/

theorem claimsStep_keeps {each : Nat × String → List Cl → S → Except String Unit}
    {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, KeepsRuns P b) {x y : List Cl × S} {o : Nat × String}
    (h : claimsInStep each bs x o = .ok y) (hx : P x.2) : P y.2 := by
  unfold claimsInStep at h
  obtain ⟨run, hr, h⟩ := bind_ok h
  obtain ⟨b, hb1, hb2⟩ := Option.bind_eq_some_iff.1 (named_ok hr)
  have hm : b ∈ bs := List.mem_of_getElem? hb1
  split at h
  · rename_i z hz
    split at h
    · cases h
      exact (hb b hm).1 _ (lookup_mem hb2) _ _ z hz hx
    · cases h
  · cases h

theorem claims_keep {each : Nat × String → List Cl → S → Except String Unit}
    {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, KeepsRuns P b) :
    ∀ (order : List (Nat × String)) (acc : Except String (List Cl × S)) (y : List Cl × S),
      (∀ x, acc = .ok x → P x.2) →
      order.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) acc = .ok y → P y.2
  | [], acc, y, ha, h => ha y h
  | o :: t, acc, y, ha, h => by
    rw [List.foldl_cons] at h
    refine claims_keep hb t _ y (fun x hx => ?_) h
    obtain ⟨a, e, h2⟩ := bind_ok hx
    exact claimsStep_keeps hb h2 (ha a e)

theorem claimsInBy_keeps {each : Nat × String → List Cl → S → Except String Unit}
    {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, KeepsRuns P b) {order : List (Nat × String)} {s : S}
    {y : List Cl × S} (h : claimsInBy each bs order s = .ok y) (hs : P s) : P y.2 :=
  claims_keep hb order _ y (fun x hx => by cases hx; exact hs) h

theorem after_keeps {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, KeepsRuns P b) :
    ∀ (order : List (Nat × String)) (acc : Except String S) (y : S), (∀ x, acc = .ok x → P x) →
      order.foldl (fun acc o => acc.bind fun x =>
        (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind
          fun run =>
            match run x with
            | .ok y => .ok y
            | .error e => .error (o.2 ++ ": " ++ e)) acc = .ok y → P y
  | [], acc, y, ha, h => ha y h
  | o :: t, acc, y, ha, h => by
    rw [List.foldl_cons] at h
    refine after_keeps hb t _ y (fun x hx => ?_) h
    obtain ⟨a, e, h2⟩ := bind_ok hx
    obtain ⟨run, hr, h3⟩ := bind_ok h2
    obtain ⟨b, hb1, hb2⟩ := Option.bind_eq_some_iff.1 (named_ok hr)
    have hm : b ∈ bs := List.mem_of_getElem? hb1
    split at h3
    · rename_i z hz
      cases h3
      exact (hb b hm).2 _ (lookup_mem hb2) _ _ hz (ha a e)
    · cases h3

theorem afterIn_keeps {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, KeepsRuns P b)
    {order : List (Nat × String)} {s s' : S} (h : afterIn bs order s = .ok s') (hs : P s) : P s' :=
  after_keeps hb order _ s' (fun x hx => by cases hx; exact hs) h

/-! ## How a supplied block is made of a kind's block -/

theorem keepsD_quiet {name : String} {chain : Nat} {link : Option Nat} {piece : Nat}
    {f : S → Except String S} (h : ∀ s s', f s = .ok s' → P s → P s') :
    KeepsD R P (roundlessBlock name chain link piece f : Block S Cl) :=
  fun s s' _ _ _ hy => h s s' hy

theorem keepsD_andThen (name : String) {p q : Block S Cl} (hp : KeepsD R P p) (hq : KeepsD R P q) :
    KeepsD R P (p.andThen name q) := by
  intro s s' rs gs hr h hs
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := bind_ok h'
  exact hq _ _ _ _ (fun r hm => hr r (List.mem_of_mem_drop hm)) h2
    (hp _ _ _ _ (fun r hm => hr r (List.mem_of_mem_take hm)) h1 hs)

theorem seatSame_ok {same : S → S → Bool} {t s s' : S} (h : seatSame same t s = .ok s') :
    s' = s := by
  unfold seatSame at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem keepsD_guarded (same : S → S → Bool) (but : Place → Bool) {b : Block S Cl}
    (hb : KeepsD R P b) : KeepsD R P (b.guarded same but) := by
  intro s s' rs gs hr h hs
  have h' : (if but b.place then b.decide s rs gs
      else (b.decide s rs gs).bind (seatSame same s)) = .ok s' := h
  split at h'
  · exact hb _ _ _ _ hr h' hs
  · obtain ⟨s₁, h1, h2⟩ := bind_ok h'
    rw [seatSame_ok h2]
    exact hb _ _ _ _ hr h1 hs

theorem keepsD_retype {Cl' : Type} {b : Block S Cl} (hb : KeepsD R P b) :
    KeepsD R P (b.retype : Block S Cl') := hb

/-- A block with another name, place or test on the plan, and the same decision. -/
theorem keepsD_under {b c : Block S Cl} (hd : c.decide = b.decide) (hb : KeepsD R P b) :
    KeepsD R P c := fun s s' rs gs hr h hs => hb s s' rs gs hr (hd ▸ h) hs

/-- A block whose own state T is born and dies inside it. Q: the property at T. -/
theorem keepsD_inside {T : Type} {Q : T → Prop} {enter : S → Except String T} {b : Block T Cl}
    {leave : S → T → Except String S} (he : ∀ s t, enter s = .ok t → P s → Q t)
    (hb : ∀ t t' rs gs, (∀ r ∈ rs, R r) → b.decide t rs gs = .ok t' → Q t → Q t')
    (hl : ∀ s t s', leave s t = .ok s' → P s → Q t → P s') : KeepsD R P (b.inside enter leave) := by
  intro s s' rs gs hr h hs
  have h' : (enter s).bind (fun t => (b.decide t rs gs).bind (leave s)) = .ok s' := h
  obtain ⟨t, h1, h2⟩ := bind_ok h'
  obtain ⟨t', h3, h4⟩ := bind_ok h2
  exact hl _ _ _ h4 hs (hb _ _ _ _ hr h3 (he _ _ h1 hs))

theorem keepsRuns_bare {b : Block S Cl} (h : b.hasNoClaimsAndNothingAfter = true) : KeepsRuns P b := by
  simp only [Block.hasNoClaimsAndNothingAfter, Bool.and_eq_true, List.isEmpty_iff] at h
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rw [h.1] at hc; cases hc
  · rw [h.2] at hc; cases hc

theorem keepsRuns_guarded (same : S → S → Bool) (but : Place → Bool) {b : Block S Cl}
    (hb : KeepsRuns P b) : KeepsRuns P (b.guarded same but) := by
  refine ⟨fun c hc n s y h hs => ?_, fun c hc s s' h hs => ?_⟩
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y0, h1, h2⟩ := bind_ok h
    cases hm : seatSame same s y0.2 with
    | error e => rw [hm] at h2; cases h2
    | ok u =>
      rw [hm] at h2
      cases h2
      exact hb.1 c0 hc0 n s y0 h1 hs
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    obtain ⟨s₁, h1, h2⟩ := bind_ok h
    rw [seatSame_ok h2]
    exact hb.2 c0 hc0 s s₁ h1 hs

/-! ## A link, a chain -/

variable (R P)

/-- What is asked of a link. -/
structure LinkKeeps (L : Link S Cl) : Prop where
  lay : ∀ s s', L.lay s = .ok s' → P s → P s'
  hearD : ∀ b ∈ L.hear, KeepsD R P b
  hearR : ∀ b ∈ L.hear, KeepsRuns P b
  batch : ∀ f : S → Except String (List Cl × S), (∀ s y, f s = .ok y → P s → P y.2) →
    KeepsD R P (L.batch f)
  close : ∀ b ∈ L.close, KeepsD R P b
  clear : ∀ s s', L.clear s = .ok s' → P s → P s'

/-- What is asked of a chain. -/
structure ChainKeeps (c : Chain S Cl) : Prop where
  first : KeepsD R P c.first
  front : ∀ b ∈ c.front, KeepsD R P b
  links : ∀ L ∈ c.links, LinkKeeps R P L
  back : ∀ b ∈ c.back, KeepsD R P b
  last : KeepsD R P c.last

variable {R P}

theorem linkKeeps_of {L : Link S Cl} (h : Keeps.LinkKeeps (Keeps.ofInv P) L) : LinkKeeps R P L where
  lay := h.1
  hearD := fun b hb => keepsD_of_decides (h.2.1 b hb).1
  hearR := fun b hb => keepsRuns_of_whole (h.2.1 b hb)
  batch := fun f hf => keepsD_of_decides (h.2.2.1 f hf)
  close := fun b hb => keepsD_of_decides (h.2.2.2.1 b hb)
  clear := h.2.2.2.2

theorem chainKeeps_of {c : Chain S Cl} (h : Keeps.ChainKeeps (Keeps.ofInv P) c) :
    ChainKeeps R P c where
  first := keepsD_of_decides h.1
  front := fun b hb => keepsD_of_decides (h.2.1 b hb)
  links := fun L hL => linkKeeps_of (h.2.2.1 L hL)
  back := fun b hb => keepsD_of_decides (h.2.2.2.1 b hb)
  last := keepsD_of_decides h.2.2.2.2

theorem runBehind_keeps {L : Link S Cl} (h : LinkKeeps R P L) {s s' : S}
    (hy : L.runBehind s = .ok s') (hs : P s) : P s' := by
  unfold Link.runBehind at hy
  split at hy
  · exact afterIn_keeps h.hearR hy hs
  · cases hy

theorem link_flat_keeps {L : Link S Cl} (h : LinkKeeps R P L) : ∀ b ∈ L.blocksInOrder, KeepsD R P b := by
  intro b hb
  unfold Link.blocksInOrder at hb
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · exact fun s s' _ _ _ hy => h.lay s s' hy
  · exact h.hearD b hb
  · exact h.batch _ fun s y hy hs => claimsInBy_keeps h.hearR hy hs
  · exact keepsD_quiet fun s s' hy hs => runBehind_keeps h hy hs
  · exact h.close b hb
  · exact keepsD_quiet h.clear

theorem chain_flat_keeps {c : Chain S Cl} (h : ChainKeeps R P c) : ∀ b ∈ c.blocksInOrder, KeepsD R P b := by
  intro b hb
  unfold Chain.blocksInOrder at hb
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | ((⟨a, ha, rfl⟩ | ⟨L, hL, hb⟩) | ⟨a, ha, rfl⟩) | rfl
  · exact h.first
  · exact h.front a ha
  · exact link_flat_keeps (h.links L hL) b hb
  · exact h.back a ha
  · exact h.last

/-! ## The step, the fold, a chain's fold -/

theorem step_keeps (hR : ∀ r, R r → R (noDigest r)) {b : Block S Cl} (hb : KeepsD R P b) {ft : Nat}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : Nat} (hr : ∀ r ∈ rs, R r)
    (h : b.step ft s rs cols = .ok (s', k)) (hs : P s) : P s' := by
  unfold Block.step at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i t ht
        cases h
        refine hb _ _ _ _ (fun r hm => ?_) ht hs
        obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hm
        exact hR r0 (hr r0 h0)

theorem fold_keeps (hR : ∀ r, R r → R (noDigest r)) (ft : Nat) :
    ∀ (bs : List (Block S Cl)) (s s' : S) (rs rs' : List Fmt.RoundView) (cols cols' : List OpenedColumn),
    (∀ b ∈ bs, KeepsD R P b) → (∀ r ∈ rs, R r) →
    foldBlocks ft bs s rs cols = .ok (s', rs', cols') → P s → P s'
  | [], s, s', rs, rs', cols, cols', _, _, h, hs => by
    simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  | b :: l, s, s', rs, rs', cols, cols', hb, hr, h, hs => by
    unfold foldBlocks at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i t k ht
        simp only [List.splitAt_eq] at ht h
        exact fold_keeps hR ft l t s' _ rs' _ cols' (fun c hc => hb c (List.mem_cons_of_mem _ hc))
          (fun r hm => hr r (List.mem_of_mem_drop hm)) h
          (step_keeps hR (hb b List.mem_cons_self) (fun r hm => hr r (List.mem_of_mem_take hm)) ht
            hs)

theorem chainAt_keeps (hR : ∀ r, R r → R (noDigest r)) {name : String} {ft : Nat}
    {bs : List (Block S Cl)} {s s' : S} {v : Fmt.View} (hb : ∀ b ∈ bs, KeepsD R P b)
    (hr : ∀ r ∈ v.rounds, R r) (h : chainAt name ft bs s v = .ok s') (hs : P s) : P s' := by
  unfold chainAt at h
  split at h
  · cases h
  · split at h
    · rename_i e
      cases h
      exact fold_keeps hR ft bs s _ _ _ _ _ hb hr e hs
    · cases h
    · cases h

end VerifiableInference.Desc.Keeps1

#print axioms VerifiableInference.Desc.Keeps1.chain_flat_keeps
#print axioms VerifiableInference.Desc.Keeps1.chainAt_keeps
#print axioms VerifiableInference.Desc.Keeps1.keepsRuns_guarded
#print axioms VerifiableInference.Desc.Keeps1.chainKeeps_of
