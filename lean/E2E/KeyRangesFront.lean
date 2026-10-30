-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesFront.lean: IN FRONT OF THE KEY FILE's TEST ON THE RANGES NO DECLARED ROUND OPENS A
TREE OR READS A STORED TABLE. So the verifier's state there is made of the rounds shown alone: no
column is read on the way. Whoever wants that state as a function of what stands in front of the
test (the input, the challenges heard, the rounds shown) can replay the verifier's own sub-protocols
over these rounds. Statements and proofs, off the description's own text
(Johnson/Desc/Key/Chain1.lean, One.lean, Link.lean; Johnson/Desc/K1/Send.lean;
Johnson/Desc/First/Look/K3LookupGeneral.lean).

  `Dry`          a declared round opens no tree and reads no stored table
  `link_dry`, `k1_dry`, **`pre_dry`**   every round of a lookup's link and of a sending is so; every
                 round of what stands in front of the ranges' test (`keyFirstPre`,
                 Johnson/Desc/K12/Law/SitsKeyChains.lean):
                 the two sendings, the lookups' links, the laying of the lookups' rows: AT ALL
                 LETTERS: no scope is asked
  `take_of_cut`, `length_of_cut`   two lemmas on a list that is cut at a member
  `pre_length`, **`take15`**   in scope that list has fifteen sub-protocols: it is the first
                 fifteen of the chain's flat list
  `readsOf_dry`   dry rounds read nothing, whatever tables are at hand
  **`colsTo15`**   so at the first chain's thread (`laid₁`, E2E/KeyRest.lean), at the border 15, the
                 columns that the sub-protocols in front read are none

Limits. On the description's declared rounds alone. Nothing on what the rounds show. Nothing on
completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place Link Chain)
open VerifiableInference.Desc.Key (Xi FirstState Claim lookupLink lookupPlace lookupsOf firstChain
  layRows)
open H2K.JointK (rngEntry keyFirstPre keyFirstPost keyFirst_cut)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open AtPublicFiles.KeyBook (places_named fullFirst rngPlace)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- A declared round opens no tree and reads no stored table. -/
def Dry (d : Fmt.DeclaredRound) : Prop := d.stored = [] ∧ d.opens = []

/-- Every round of a lookup's link is dry. -/
theorem link_dry (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : Nat)
    (x : VerifiableInference.Desc.Key.Lookup) :
    ∀ d ∈ (lookupLink one set i x).blocksInOrder.flatMap (·.rounds), Dry d := by
  intro d hd
  have e : (lookupLink one set i x).blocksInOrder.flatMap (·.rounds) =
      (((lookupPlace set i x).entries.getD []).map fun e => ({ entry := e } : Fmt.DeclaredRound)) ++
        [] := rfl
  rw [e, List.append_nil] at hd
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hd
  exact ⟨rfl, rfl⟩

/-- A sending's two rounds are dry. -/
theorem k1_dry (P : VerifiableInference.Desc.K1.Par) :
    ∀ d ∈ VerifiableInference.Desc.K1.rounds P ++ [], Dry d := by
  intro d hd
  unfold VerifiableInference.Desc.K1.rounds at hd
  simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **Every round in front of the ranges' test is dry.** -/
theorem pre_dry (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) :
    ∀ d ∈ (keyFirstPre one D told set N).flatMap (·.rounds), Dry d := by
  intro d hd
  obtain ⟨b, hb, hd⟩ := List.mem_flatMap.1 hd
  unfold keyFirstPre at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · -- the index masks' sending: the kind's two rounds
        have hd' : d ∈ VerifiableInference.Desc.K1.rounds _ ++ [] := hd
        exact k1_dry _ d hd'
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        have hc' : c ∈ [VerifiableInference.Desc.Key.sendOwnMessage one
            VerifiableInference.Desc.Key.pieces
            (VerifiableInference.Desc.Key.groupsTold told
              (VerifiableInference.Desc.Key.rootsBefore D 2)
              (VerifiableInference.Desc.Key.rootsAt D 2))] := hc
        obtain rfl := List.mem_singleton.1 hc'
        have hd' : d ∈ VerifiableInference.Desc.K1.rounds _ ++ [] := hd
        exact k1_dry _ d hd'
    · obtain ⟨Lk, hL, hb⟩ := List.mem_flatMap.1 hb
      have hL' : Lk ∈ (lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1 := hL
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hL'
      exact link_dry one set x.2 x.1 d (List.mem_flatMap.2 ⟨b, hb, hd⟩)
  · obtain rfl := List.mem_singleton.1 hb
    cases hd

/-- A list cut behind n members: its first n. -/
theorem take_of_cut {α : Type} (l pre post : List α) (a : α) (n : Nat) (h : l = pre ++ a :: post)
    (hn : pre.length = n) : l.take n = pre := by
  subst h
  exact List.take_left' hn

/-- A list cut at a member whose image stands once, at the place n, in the list of images. -/
theorem length_of_cut {α β : Type} [DecidableEq β] (f : α → β) (l pre post : List α) (a : α)
    (L : List β) (b : β) (n : Nat) (h : l = pre ++ a :: post) (hm : l.map f = L) (hn : L.Nodup)
    (ha : f a = b) (hi : L.idxOf b = n) : pre.length = n := by
  subst h
  rw [List.map_append, List.map_cons, ha] at hm
  subst hm
  have hno : b ∉ pre.map f := fun hmem =>
    List.disjoint_of_nodup_append hn hmem List.mem_cons_self
  rw [List.idxOf_append_of_notMem hno, List.idxOf_cons_self, List.length_map] at hi
  exact hi

/-- Dry rounds read nothing. -/
theorem readsOf_dry (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (l : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), (∀ d ∈ l, Dry d) →
      readsOf chain ft stored tree l ds = []
  | [], _, _ => by
    unfold readsOf
    rfl
  | _ :: _, [], _ => by
    unfold readsOf
    rfl
  | d :: l, R :: Rs, h => by
    unfold readsOf
    rw [(h d List.mem_cons_self).1, (h d List.mem_cons_self).2,
      readsOf_dry chain ft stored tree l Rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

section Scope
variable {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- In scope fifteen sub-protocols stand in front of the ranges' test. -/
theorem pre_length (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    (keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).length = 15 :=
  length_of_cut (fun b : Block FirstState Claim => (b.place, b.rounds.length))
    (keyFileDescription Xs N Pl).first.blocksInOrder _ _ _ fullFirst (rngPlace, 23) 15 (keyFirst_cut _ _ _ _ _)
    (places_named scope h).1 (by decide)
    (by
      have e := member15 scope h
      have q := congrArg (·[15]?) (places_named scope h).1
      unfold rowsOf at q
      have q' : ((keyFileDescription Xs N Pl).first.blocksInOrder[15]?).map (fun b => (b.place, b.rounds.length)) =
          fullFirst[15]? := by
        rw [← List.getElem?_map]
        exact q
      have q'' : (some (rngEntry Xs.Y.k.oneTime N)).map
          (fun b : Block FirstState Claim => (b.place, b.rounds.length)) = fullFirst[15]? :=
        (congrArg (Option.map fun b : Block FirstState Claim => (b.place, b.rounds.length))
          e).symm.trans q'
      have e15 : fullFirst[15]? = some (rngPlace, 23) := by decide
      exact Option.some.inj (q''.trans e15))
    (by decide)

/-- **The first fifteen of the flat list are what stands in front of the ranges' test.** -/
theorem take15 (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    (keyFileDescription Xs N Pl).first.blocksInOrder.take 15 =
      keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N :=
  take_of_cut _ _ _ _ 15 (keyFirst_cut _ _ _ _ _) (pre_length scope h)

end Scope

section Laid
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀)
  (rc : Rc) (x : Xi) (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **At the border 15 the sub-protocols in front have read no column.** -/
theorem colsTo15 (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (m : Mid (Local W₀ Rc Xi Unit) X') (E : Env) :
    (laid₁ Xs N Pl L w₀ rc x hs tb).colsTo 15 m E = .ok [] := by
  unfold Thread.colsTo
  rw [readsOf_dry _ _ _ _ _ _ (by
    intro d hd
    have hd' : d ∈ ((keyFileDescription Xs N Pl).first.blocksInOrder.take 15).flatMap (·.rounds) := hd
    rw [take15 scope h] at hd'
    exact pre_dry _ _ _ _ _ d hd')]
  rfl

end Laid

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.link_dry
#print axioms AtPublicFiles.KeyThread.k1_dry
#print axioms AtPublicFiles.KeyThread.pre_dry
#print axioms AtPublicFiles.KeyThread.take_of_cut
#print axioms AtPublicFiles.KeyThread.length_of_cut
#print axioms AtPublicFiles.KeyThread.readsOf_dry
#print axioms AtPublicFiles.KeyThread.pre_length
#print axioms AtPublicFiles.KeyThread.take15
#print axioms AtPublicFiles.KeyThread.colsTo15
