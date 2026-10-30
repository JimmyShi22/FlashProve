--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupAround.lean: the sub-protocols WITHOUT A ROUND that stand around a lookup in the first
chain of the key file's IOP as written in Lean (Johnson/Desc/Key/Link.lean): under which conditions
on the carried state each accepts, and which state it leaves. General in the lookup, the setting and
the chain's public values. Statements and proofs; nothing is evaluated.

Why. A lookup's link lies in the chain's blocksInOrder list as six sub-protocols: laid · `caller` · the
lookup (`K3.lookupKind`: E2E/KeyLookupHears.lean) · `layer` · behind the batching's place · cleared;
behind both links stands `layRows`. Whoever shows that the verifier accepts an honest run has to
pass each of them.

What is shown.
  `Room d o n`: message o is there, and its ledger of mask entries is open with n entries left at
    least. **`takeMasks_of_room`**: then it hands out n entries; the other messages' ledgers stay.
  `fromKeys_length`, `fromKeys_true`, **`homes_size`**: at every face whose parts have a level each:
    the library's table of marks (`K3.fromKeys`) has `Face.slots` members, of which two a part are
    marked; so EVERY HIDDEN VALUE HAS A HOME.
  **`caller_decide`**: no ledger open · i lookups behind · the two messages differ · room in both
    ledgers ⟹ `caller` accepts, and lays the fresh ledger and the homes.
  `link_lay`, `link_behind`, `link_clear`: the link's own three steps.
  `Scoped n a`: the form a names no entry of a virtual row, and slots below n alone.  
    `maskSide_some`: such a form has a row where every slot below n has a home and is filled.
  **`link_claims`**: what the link's runs of claims gather, and the ledger behind them.
  `rows_some`, `keyClaims_some`: every claim has a row; every part's form has a claim on its keys.
  **`Left p g G cl G₂`**: TEN FACTS ON WHAT WAS HEARD, which `layer` needs.   **`layer_decide`**:
    under them `layer` accepts, and writes the lookup's rows and its claims on keys, which are
    named.
  `layRows_decide`: its three tests as premises.
  `leftB`, `left_of_B`: the ten facts as one test with code (E2E/KeyLookupAroundToy.lean evaluates
    it).

Limits.
- `Left` IS A PREMISE. That the hearing of an honest run (or of any run that `hearV` accepts) leaves
  these ten facts is not shown. They are facts on counts, marks and the slots that forms name; no
  sent value is compared in them: that is by reading.
- `Room` is a premise: that the two sendings in front leave so many entries is not shown.
- `layRows_decide` restates that sub-protocol's tests: it says little.
- The states are not chained: no theorem walks the six sub-protocols of a link in a row.
- That the rows which `layer` writes HOLD of an honest prover's mask entries, keys and bits is not
  touched.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyLookupHears

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block named need)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP takeMaskL ok has)

/-! ## 1. A message's ledger of mask entries hands out what it has left -/

section Ledger
variable {L : Type}

/-- Message o is there, and its ledger is open with n entries left at least. -/
def Room (d : DState L) (o n : ℕ) : Prop :=
  ∃ x l, d.st.oracles[o]? = some x ∧ x.ledger = some l ∧ l.closed = false ∧ n ≤ l.left

theorem takeMask_of_room {d : DState L} {o n : ℕ} (h : Room d o (n + 1)) :
    ∃ i d', takeMaskP d o = some (i, d') ∧ Room d' o n ∧
      ∀ o' m, o' ≠ o → Room d o' m → Room d' o' m := by
  obtain ⟨x, l, hx, hl, hc, hn⟩ := h
  have hok : ok (takeMaskL d.st o) = true := by
    have h0 : 0 < l.left := by omega
    simp [ok, takeMaskL, has, hx, hl, hc, h0]
  have ho : o < d.st.oracles.size := by
    rcases Nat.lt_or_ge o d.st.oracles.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hx
      cases hx
  let n0 := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next
  let l₁ : Ledger := { l with next := n0 + 1, left := l.left - 1 }
  let d₁ : DState L := { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
    { x with ledger := some l₁ } } }
  have ht : takeMaskP d o = some (n0, d₁) := by
    unfold takeMaskP
    rw [if_pos hok, hx]
    simp only [Option.bind_some, hl, Option.map_some]
    rfl
  refine ⟨n0, d₁, ht, ⟨{ x with ledger := some l₁ }, l₁, ?_, rfl, hc, ?_⟩, ?_⟩
  · show (d.st.oracles.modify o _)[o]? = _
    rw [Array.getElem?_modify, if_pos rfl, hx]
    rfl
  · show n ≤ l.left - 1
    omega
  · rintro o' m hne ⟨x', l', hx', r⟩
    refine ⟨x', l', ?_, r⟩
    show (d.st.oracles.modify o _)[o']? = _
    rw [Array.getElem?_modify, if_neg (fun e => hne e.symm)]
    exact hx'

theorem takeInto_of_room {o : ℕ} : ∀ (n : ℕ) (d : DState L) (acc : Array ℕ), Room d o n →
    ∃ l d', takeMasksInto o n d acc = some (l, d') ∧ l.length = acc.size + n ∧
      ∀ o' m, o' ≠ o → Room d o' m → Room d' o' m
  | 0, d, acc, _ => ⟨acc.toList, d, rfl, by simp, fun _ _ _ h => h⟩
  | n + 1, d, acc, h => by
    obtain ⟨i, d₁, h1, r1, k1⟩ := takeMask_of_room h
    obtain ⟨l, d', h2, e2, k2⟩ := takeInto_of_room n d₁ (acc.push i) r1
    refine ⟨l, d', ?_, ?_, fun o' m hne r => k2 o' m hne (k1 o' m hne r)⟩
    · unfold takeMasksInto
      rw [h1]
      exact h2
    · rw [e2, Array.size_push]
      omega

/-- **A ledger with n entries left hands out n**; the other messages' ledgers stay. -/
theorem takeMasks_of_room {d : DState L} {o n : ℕ} (h : Room d o n) :
    ∃ l d', takeMasksP d o n = some (l, d') ∧ l.length = n ∧
      ∀ o' m, o' ≠ o → Room d o' m → Room d' o' m := by
  obtain ⟨l, d', h1, e, k⟩ := takeInto_of_room n d #[] h
  exact ⟨l, d', h1, by simpa using e, k⟩

end Ledger

/-! ## 2. Every hidden value has a home -/

theorem homesFrom_length : ∀ (bs : List Bool) (o k : List Slot), bs.count false ≤ o.length →
    bs.count true ≤ k.length → (homesFrom bs o k).length = bs.length
  | [], _, _, _, _ => by simp [homesFrom]
  | false :: bs, [], _, h, _ => by simp at h
  | false :: bs, s :: o, k, h, h' => by
    have h1 : bs.count false ≤ o.length := by simpa using h
    have h2 : bs.count true ≤ k.length := by simpa using h'
    simp [homesFrom, homesFrom_length bs o k h1 h2]
  | true :: bs, _, [], _, h => by simp at h
  | true :: bs, o, s :: k, h, h' => by
    have h1 : bs.count false ≤ o.length := by simpa using h
    have h2 : bs.count true ≤ k.length := by simpa using h'
    simp [homesFrom, homesFrom_length bs o k h1 h2]

theorem own_length (n : ℕ) : (own n).length = n := List.length_replicate

theorem own_true (n : ℕ) : (own n).count true = 0 :=
  List.count_eq_zero.2 fun h => by cases List.eq_of_mem_replicate h

/-- The marks of one level of a key tree with v levels. -/
def lvl (v k : ℕ) : List Bool :=
  if k + 1 == v then own (2 * k + 3) ++ [true, true] else own (2 * k + 5)

theorem lvl_length (v k : ℕ) : (lvl v k).length = 2 * k + 5 := by
  unfold lvl
  split
  · rw [List.length_append, own_length]
    rfl
  · exact own_length _

theorem tree_length (v : ℕ) :
    ((List.range v).flatMap (lvl v)).length = ((List.range v).map fun k => 2 * k + 5).sum := by
  rw [List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun k _ => lvl_length v k)

theorem tree_true : ∀ v, 1 ≤ v → ((List.range v).flatMap (lvl v)).count true = 2
  | 0, h => absurd h (by decide)
  | n + 1, _ => by
    rw [List.range_succ, List.flatMap_append, List.count_append]
    have h0 : ((List.range n).flatMap (lvl (n + 1))).count true = 0 := by
      refine List.count_eq_zero.2 fun h => ?_
      obtain ⟨k, hk, ht⟩ := List.mem_flatMap.1 h
      have hne : (k + 1 == n + 1) = false := by
        have := List.mem_range.1 hk
        simp
        omega
      unfold lvl at ht
      rw [hne] at ht
      cases List.eq_of_mem_replicate ht
    rw [h0]
    simp [lvl, own_true]

theorem fromKeys_eq (f : Face) : fromKeys f =
    own (7 + 6 * (f.planes - 2) + 5 * (f.parts.length - 1)) ++
      (f.parts.flatMap fun v => (List.range v).flatMap (lvl v)) ++
      own (((List.range f.d).map fun l => 2 * (f.mu + l) + 5).sum +
        (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1)) := rfl

theorem fromKeys_length (f : Face) : (fromKeys f).length = f.slots := by
  rw [fromKeys_eq, List.length_append, List.length_append, own_length, own_length,
    List.length_flatMap]
  have e : (f.parts.map fun v => ((List.range v).flatMap (lvl v)).length) =
      f.parts.map fun v => ((List.range v).map fun k => 2 * k + 5).sum :=
    List.map_congr_left fun v _ => tree_length v
  rw [e]
  unfold Face.slots
  omega

theorem fromKeys_true {f : Face} (h : ∀ v ∈ f.parts, 1 ≤ v) :
    (fromKeys f).count true = 2 * f.parts.length := by
  rw [fromKeys_eq, List.count_append, List.count_append, own_true, own_true, List.count_flatMap]
  have e : (f.parts.map (List.count true ∘ fun v => (List.range v).flatMap (lvl v))) =
      f.parts.map fun _ => 2 := List.map_congr_left fun v hv => tree_true v (h v hv)
  rw [e]
  simp [Nat.mul_comm]

theorem count_tf : ∀ l : List Bool, l.count true + l.count false = l.length
  | [] => rfl
  | true :: l => by
    have := count_tf l
    simp only [List.count_cons_self, List.count_cons_of_ne (by decide : true ≠ false),
      List.length_cons]
    omega
  | false :: l => by
    have := count_tf l
    simp only [List.count_cons_self, List.count_cons_of_ne (by decide : false ≠ true),
      List.length_cons]
    omega

/-- **Every hidden value has a home**: at a face whose parts have a level each: of as many entries
of the first message as there are hidden values less two a part, and two a part of the second. -/
theorem homes_size {f : Face} (h : ∀ v ∈ f.parts, 1 ≤ v) {o k : List Slot}
    (ho : o.length = f.slots - 2 * f.parts.length) (hk : k.length = 2 * f.parts.length) :
    (homes f o k).size = f.slots := by
  have ht := fromKeys_true h
  have hl := fromKeys_length f
  have hs := count_tf (fromKeys f)
  unfold homes
  rw [List.size_toArray, homesFrom_length _ _ _ (by omega) (by omega), hl]

/-! ## 3. The sub-protocol in front of a lookup's rounds -/

/-- **The sub-protocol in front of lookup i's rounds accepts**, and opens the fresh ledger: at a
state with no open ledger, i lookups behind it, and room in the two messages' ledgers of mask
entries. -/
theorem caller_decide (one : Params.OneTime) (i : ℕ) (x : Lookup) {s : FirstState}
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hv : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
    (hf : s.base.fork = none) (hk : s.base.keys.length = i)
    (hne : s.idx ≠ one.ranges.messageId)
    (h1 : Room s.d one.ranges.messageId
      ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
    (h2 : Room s.d s.idx (2 * (faceOfLkp x).parts.length)) :
    ∃ o d₁ k d₂,
      takeMasksP s.d one.ranges.messageId
        ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) = some (o, d₁) ∧
      takeMasksP d₁ s.idx (2 * (faceOfLkp x).parts.length) = some (k, d₂) ∧
      (caller one i x).decide s rs cols = .ok
        { s with
          d := d₂
          base := { s.base with
            fork := some (({} : Fork).slots (faceOfLkp x).slots), heard := none
            home := homes (faceOfLkp x) (o.map fun j => ⟨one.ranges.messageId, j⟩)
              (k.map fun j => ⟨s.idx, j⟩) } } := by
  obtain ⟨o, d₁, e1, l1, k1⟩ := takeMasks_of_room h1
  obtain ⟨k, d₂, e2, l2, -⟩ := takeMasks_of_room (k1 s.idx _ hne h2)
  refine ⟨o, d₁, k, d₂, e1, e2, ?_⟩
  have hs : (homes (faceOfLkp x) (o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
      (k.map fun j => (⟨s.idx, j⟩ : Slot))).size = (faceOfLkp x).slots :=
    homes_size hv (by rw [List.length_map, l1]) (by rw [List.length_map, l2])
  simp only [caller, quietAt, hf, hk, e1, e2, hs, named, need, Option.isNone_none,
    beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true]

/-! ## 4. The link's own three steps without a round -/

section Frame
variable (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup)

/-- The link is laid where no ledger is open. -/
theorem link_lay {s : FirstState} (hf : s.base.fork = none) :
    (lookupLink one set i x).lay s = .ok s := by
  simp only [lookupLink, hf, need, Option.isNone_none, bind, Except.bind, pure, Except.pure,
    if_true]

/-- Behind the batching's place nothing is asked. -/
theorem link_behind (s : FirstState) : (lookupLink one set i x).runBehind s = .ok s := rfl

/-- At the end the ledger, the hearing and the homes are cleared. -/
theorem link_clear (s : FirstState) : (lookupLink one set i x).clear s =
    .ok { s with base := { s.base with fork := none, heard := none, home := #[] } } := rfl

end Frame

/-! ## 5. A form over hidden values has a row where its slots have homes and are filled -/

theorem fold_some {F : Fork} {home : Array Slot} {n : ℕ} (hh : home.size = n)
    (hs : ∀ j, j < n → (F.shown j).isSome = true) :
    ∀ (l : List (ℕ × E)) (init : MaskForm × E), (∀ t ∈ l, t.1 < n) →
      (l.foldlM (fun (y : MaskForm × E) (t : ℕ × E) =>
        match home[t.1]?, F.shown t.1 with
        | some s, some v =>
          some (y.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE y.2 (mulE t.2 v))
        | _, _ => none) init).isSome = true
  | [], _, _ => rfl
  | t :: l, init, h => by
    have ht : t.1 < n := h t (List.mem_cons_self ..)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hs t.1 ht)
    rw [List.foldlM_cons, Array.getElem?_eq_getElem (hh ▸ ht), hv]
    exact fold_some hh hs l _ fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

/-- The form names no entry of a virtual row, and slots below n alone. -/
def Scoped (n : ℕ) (a : Model.Aff) : Prop :=
  a.ents.isEmpty = true ∧ ∀ t ∈ a.slots.toList, t.1 < n

theorem maskSide_some {F : Fork} {home : Array Slot} {n : ℕ} {a : Model.Aff} (hh : home.size = n)
    (hs : ∀ j, j < n → (F.shown j).isSome = true) (ha : Scoped n a) :
    (maskSide F home a).isSome = true := by
  unfold maskSide
  rw [ha.1]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [← Array.foldlM_toList]
  exact fold_some hh hs _ _ ha.2

/-! ## 6. The link's claims -/

theorem mapM_inr : ∀ l : List PlaneClaim,
    l.mapM (fun c => (some (Sum.inr c) : Option Claim)) = some (l.map Sum.inr)
  | [] => rfl
  | c :: l => by
    rw [List.mapM_cons, mapM_inr l]
    rfl

/-- **The link's claims are gathered**: at a state with the ledger G and the hearing g: the forms
that the hearing left, then the three claims on the planes; the ledger behind is the one in which
the leaves' sumcheck is closed, with the first two debts marked. -/
theorem link_claims (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup)
    {s : FirstState} {g : HeardG} {G G₂ : Fork} {cl : List PlaneClaim} {rest : K.Kc.Tape}
    (hF : s.base.fork = some G) (hg : s.base.heard = some g)
    (hu : unpaidG (G.paid g.owedObjects) g.owedPlanes = true)
    (hp : planesG (faceOfLkp x) g (G.paid g.owedObjects) [] = some (cl, G₂, rest)) :
    VerifiableInference.Desc.claimsInBy (lookupLink one set i x).each (lookupLink one set i x).hear
      (lookupLink one set i x).order s =
      .ok (g.rows.toList.map Sum.inl ++ cl.map Sum.inr,
        { s with base := { s.base with fork := some (G₂.paid g.owedPlanes) } }) := by
  simp [VerifiableInference.Desc.claimsInBy, VerifiableInference.Desc.claimsInStep, lookupLink,
    lookupKind, lookupSeat, lookupPlace, named, need, hF, hg, hu, hp, List.lookup, mapM_inr, bind,
    Except.bind, pure, Except.pure]

/-! ## 7. The sub-protocol behind a lookup's rounds -/

theorem mapM_isSome {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ a ∈ l, (f a).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a (List.mem_cons_self ..))
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1
      (mapM_isSome f l fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))
    rw [List.mapM_cons, hb, hbs]
    rfl

/-- A claim's form over hidden values is scoped. -/
def ClaimScoped (n : ℕ) : Claim → Prop
  | .inl a => Scoped n a
  | .inr c => Scoped n c.lead

theorem rowOfClaim_some {planesAt : OnBytes.Row → Tensor → OnBytes.Row} {F : Fork}
    {home : Array Slot} {n : ℕ} (turned : Bool) (hh : home.size = n)
    (hs : ∀ j, j < n → (F.shown j).isSome = true) :
    ∀ c : Claim, ClaimScoped n c → (rowOfClaim planesAt F home turned c).isSome = true
  | .inl a, h => by
    show ((maskSide F home a).map _).isSome = true
    rw [Option.isSome_map]
    exact maskSide_some hh hs h
  | .inr c, h => by
    show ((maskSide F home c.lead).map _).isSome = true
    rw [Option.isSome_map]
    exact maskSide_some hh hs h

theorem layerOrder_mem {n : ℕ} (h1 : 1 ≤ n) : ∀ t ∈ layerOrder n,
    (t.1 = true → t.2.1 < 3) ∧ (t.1 = false → t.2.1 < n) := by
  intro t ht
  simp only [layerOrder, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with ⟨j, hj, rfl⟩ | rfl | rfl | rfl | rfl <;> constructor <;> intro h <;>
    simp at h ⊢ <;> omega

theorem layerOrder_length {n : ℕ} (h1 : 1 ≤ n) : (layerOrder n).length = n + 3 := by
  simp only [layerOrder, List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  omega

theorem filter_left (objs : List Model.Aff) (cl : List PlaneClaim) :
    ((objs.map Sum.inl ++ cl.map Sum.inr : List Claim).filter fun c => c.isLeft) =
      objs.map Sum.inl := by
  simp [List.filter_append, List.filter_map, Function.comp_def]

theorem filter_right (objs : List Model.Aff) (cl : List PlaneClaim) :
    ((objs.map Sum.inl ++ cl.map Sum.inr : List Claim).filter fun c => c.isRight) =
      cl.map Sum.inr := by
  simp [List.filter_append, List.filter_map, Function.comp_def]

/-- **Every claim has a row.** -/
theorem rows_some {planesAt : OnBytes.Row → Tensor → OnBytes.Row} {F : Fork} {home : Array Slot}
    {n : ℕ} (hh : home.size = n) (hs : ∀ j, j < n → (F.shown j).isSome = true)
    {objs : List Model.Aff} {cl : List PlaneClaim} (h3 : cl.length = 3) (h1 : 1 ≤ objs.length)
    (ho : ∀ a ∈ objs, Scoped n a) (hc : ∀ c ∈ cl, Scoped n c.lead) :
    (rowsInOrder planesAt (layerOrder objs.length) F home
      (objs.map Sum.inl ++ cl.map Sum.inr)).isSome = true := by
  unfold rowsInOrder
  rw [filter_left, filter_right]
  have e1 : ((cl.map Sum.inr : List Claim).length != 3 ||
      (layerOrder objs.length).length != (objs.map Sum.inl ++ cl.map Sum.inr : List Claim).length) =
      false := by
    rw [layerOrder_length h1]
    simp [h3]
  simp only [e1, Bool.false_eq_true, if_false]
  refine mapM_isSome _ _ fun t ht => ?_
  obtain ⟨k1, k2⟩ := layerOrder_mem h1 t ht
  cases hb : t.1 with
  | true =>
    have hlt : t.2.1 < (cl.map Sum.inr : List Claim).length := by
      rw [List.length_map, h3]
      exact k1 hb
    simp only [if_true]
    rw [List.getElem?_eq_getElem hlt]
    refine rowOfClaim_some _ hh hs _ ?_
    rw [List.getElem_map]
    exact hc _ (List.getElem_mem _)
  | false =>
    have hlt : t.2.1 < (objs.map Sum.inl : List Claim).length := by
      rw [List.length_map]
      exact k2 hb
    simp only [Bool.false_eq_true, if_false]
    rw [List.getElem?_eq_getElem hlt]
    refine rowOfClaim_some _ hh hs _ ?_
    rw [List.getElem_map]
    exact ho _ (List.getElem_mem _)

theorem zipIdx_fst {α : Type} {P : α → Prop} : ∀ (l : List α) (k : ℕ), (∀ a ∈ l, P a) →
    ∀ y ∈ l.zipIdx k, P y.1
  | [], _, _, _, hy => by cases hy
  | a :: l, k, h, y, hy => by
    rw [List.zipIdx_cons] at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h a (List.mem_cons_self ..)
    · exact zipIdx_fst l (k + 1) (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) y hy

/-- **Every part's form has a claim on its keys.** -/
theorem keyClaims_some {x : Lookup} {F : Fork} {home : Array Slot} {n : ℕ} {g : HeardG}
    (hh : home.size = n) (hs : ∀ j, j < n → (F.shown j).isSome = true)
    (hk : ∀ k ∈ g.keys, Scoped n k.2) : (keyClaims x F home g).isSome = true := by
  unfold keyClaims
  refine mapM_isSome _ _ fun y hy => ?_
  rw [Option.isSome_map]
  exact maskSide_some hh hs (zipIdx_fst (P := fun k => Scoped n k.2) g.keys 0 hk y hy)

/-- **What the sub-protocol behind a lookup's rounds needs of what was heard**: ten facts, each on
counts, on marks in the ledger, or on which slots a form names; none compares a sent value (by
reading of `planesG`, `Fl.pscRow`, `doneG`, `unpaidG`). p: the place. g, G: what was heard, and the
ledger behind the hearing. cl, G₂: the three claims on the planes, and the ledger in which the
leaves' sumcheck is closed. -/
structure Left (p : PG) (g : HeardG) (G : Fork) (cl : List PlaneClaim) (G₂ : Fork) : Prop where
  /-- the debt «claims on the planes» is unmarked -/
  unpaid : unpaidG (G.paid g.owedObjects) g.owedPlanes = true
  /-- the leaves' sumcheck can be closed -/
  planes : ∃ rest, planesG p.face g (G.paid g.owedObjects) [] = some (cl, G₂, rest)
  three : cl.length = 3
  /-- the ledger has room for just the lookup's hidden values -/
  room : G₂.ns = p.face.slots
  first : p.first = 0
  /-- a form at least was left; every form names slots of the lookup alone -/
  one : 1 ≤ g.rows.toList.length
  rows : ∀ a ∈ g.rows.toList, Scoped p.face.slots a
  leads : ∀ c ∈ cl, Scoped p.face.slots c.lead
  keys : ∀ k ∈ g.keys, Scoped p.face.slots k.2
  /-- nothing of the lookup is left open, once the third debt is marked -/
  done : doneG p g ((G₂.paid g.owedPlanes).paid g.owedJoin) = true

theorem Left.shown {p : PG} {g : HeardG} {G G₂ : Fork} {cl : List PlaneClaim}
    (h : Left p g G cl G₂) (j : ℕ) (hj : j < p.face.slots) :
    ((G₂.paid g.owedPlanes).shown j).isSome = true := by
  have hd := h.done
  unfold doneG at hd
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hd
  have hg : G₂.gotF.getD j false = true := by
    have := hd.1.2 j hj
    rw [h.first, Nat.zero_add] at this
    exact this
  show (if decide (j < G₂.ns) && G₂.gotF.getD j false then some (G₂.vp.getD j zeroE)
    else none).isSome = true
  rw [h.room, hg, decide_eq_true hj]
  rfl

/-- **The sub-protocol behind lookup i's rounds accepts**: at a state with the ledger and the
hearing that the lookup's sub-protocol has laid, a home for every hidden value, and the facts
`Left`: it writes the lookup's rows and its claims on keys. -/
theorem layer_decide (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup)
    {s : FirstState} {g : HeardG} {G G₂ : Fork} {cl : List PlaneClaim} (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64))) (hF : s.base.fork = some G)
    (hg : s.base.heard = some g) (hh : s.base.home.size = (faceOfLkp x).slots)
    (h : Left (lookupPlace set i x) g G cl G₂) :
    ∃ rows keys,
      rowsInOrder (Wf.planesAt one.ranges one.codes i) (layerOrder g.rows.toList.length)
        (G₂.paid g.owedPlanes) s.base.home (g.rows.toList.map Sum.inl ++ cl.map Sum.inr) =
        some rows ∧
      keyClaims x (G₂.paid g.owedPlanes) s.base.home g = some keys ∧
      ((lookupLink one set i x).batch (VerifiableInference.Desc.claimsInBy
        (lookupLink one set i x).each (lookupLink one set i x).hear
        (lookupLink one set i x).order)).decide s rs cols = .ok
        { s with base := { s.base with
            fork := some ((G₂.paid g.owedPlanes).paid g.owedJoin)
            rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } } := by
  obtain ⟨rest, hp⟩ := h.planes
  have hc := link_claims one set i x hF hg h.unpaid hp
  obtain ⟨rows, hr⟩ := Option.isSome_iff_exists.1 (rows_some
    (planesAt := Wf.planesAt one.ranges one.codes i) hh h.shown h.three h.one h.rows h.leads)
  obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 (keyClaims_some (x := x) hh h.shown h.keys)
  refine ⟨rows, keys, hr, hk, ?_⟩
  have hl : ((g.rows.toList.map Sum.inl ++ cl.map Sum.inr : List Claim).filter
      fun c => c.isLeft).length = g.rows.toList.length := by
    rw [filter_left, List.length_map]
  show (layer one set i x _).decide s rs cols = _
  simp only [layer, quietAt, hc, hg, hl, hr, hk, h.done, named, need, bind, Except.bind, pure,
    Except.pure, if_true]

/-- **The sub-protocol that lays all lookups' rows onto the ranges' group accepts**: where all
lookups have laid their rows, the group holds no open row and its test has not begun, and the rows
fit. -/
theorem layRows_decide (one : Params.OneTime) {s : FirstState} {d : PlainState}
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h1 : s.base.rows.length = (lookupsOf one).length)
    (h2 : ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun) = true)
    (h3 : VerifiableInference.Desc.Ground.addRowsP s.d s.grp s.base.rows.flatten = some d) :
    (layRows one).decide s rs cols = .ok { s with d := d } := by
  simp only [layRows, quietAt, h1, h2, h3, named, need, beq_self_eq_true, bind, Except.bind, pure,
    Except.pure, if_true]

/-! ## 8. The ten facts as a test with code -/

def scopedB (n : ℕ) (a : Model.Aff) : Bool :=
  a.ents.isEmpty && a.slots.toList.all fun t => decide (t.1 < n)

theorem scoped_of_B {n : ℕ} {a : Model.Aff} (h : scopedB n a = true) : Scoped n a := by
  unfold scopedB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

/-- The ten facts, as one test. -/
def leftB (p : PG) (g : HeardG) (G : Fork) : Bool :=
  unpaidG (G.paid g.owedObjects) g.owedPlanes &&
    match planesG p.face g (G.paid g.owedObjects) [] with
    | none => false
    | some y =>
      y.1.length == 3 && y.2.1.ns == p.face.slots && p.first == 0 &&
        decide (1 ≤ g.rows.toList.length) && g.rows.toList.all (scopedB p.face.slots) &&
        y.1.all (fun c => scopedB p.face.slots c.lead) &&
        g.keys.all (fun k => scopedB p.face.slots k.2) &&
        doneG p g ((y.2.1.paid g.owedPlanes).paid g.owedJoin)

theorem left_of_B {p : PG} {g : HeardG} {G : Fork} (h : leftB p g G = true) :
    ∃ cl G₂, Left p g G cl G₂ := by
  unfold leftB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hu, h⟩ := h
  cases hp : planesG p.face g (G.paid g.owedObjects) [] with
  | none => rw [hp] at h; cases h
  | some y =>
    rw [hp] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h3, hn⟩, hf⟩, h1⟩, hr⟩, hl⟩, hk⟩, hd⟩ := h
    exact ⟨y.1, y.2.1, hu, ⟨y.2.2, hp⟩, h3, hn, hf, h1, fun a ha => scoped_of_B (hr a ha),
      fun c hc => scoped_of_B (hl c hc), fun k hk' => scoped_of_B (hk k hk'), hd⟩

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.takeMasks_of_room
#print axioms AtPublicFiles.KeyLookup.homes_size
#print axioms AtPublicFiles.KeyLookup.caller_decide
#print axioms AtPublicFiles.KeyLookup.link_lay
#print axioms AtPublicFiles.KeyLookup.link_behind
#print axioms AtPublicFiles.KeyLookup.link_clear
#print axioms AtPublicFiles.KeyLookup.maskSide_some
#print axioms AtPublicFiles.KeyLookup.link_claims
#print axioms AtPublicFiles.KeyLookup.rows_some
#print axioms AtPublicFiles.KeyLookup.keyClaims_some
#print axioms AtPublicFiles.KeyLookup.layer_decide
#print axioms AtPublicFiles.KeyLookup.layRows_decide
#print axioms AtPublicFiles.KeyLookup.left_of_B
