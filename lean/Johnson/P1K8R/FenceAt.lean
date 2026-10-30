-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FenceAt.lean: THE FENCE AT THE STATE's OWN LIST, AT THE PROOF
FILE's 25 PLACES OF THE APPROXIMATE RANGE PROOF (our files: the smallness test), IN SCOPE: every
seat that the sub-protocol names lies in a tree below the first tree of the piece that holds it. A
JOINING of P1K8S.sitsAt_open (OrderAtSeat.lean: at each place the sub-protocol that the seat
lays has LikeP) with named_seats_below_fits (Johnson/Desc/First/K8/LawFenceBase.lean).
WHAT IS SAID.
  k08_fence   in scope, at an opening's letters, at rows of pieces T that hold the written IOP's
              sub-protocols (OfDesc) and fit it (Three.Fits), where its data are made and its test
              on the plan says yes: at each x of the 25 places, at the piece q at number
              14 * x.1 + x.2 + 2: Named.namedB (k8ParW Z G₀ Xl x.1).toPar S₀ book tl L = true
              gives, at every i, (Named.seatFn rad S₀ book tl L i).1 < q.base.
LIMITS. OfDesc, Three.Fits, "the data are made" and "the plan's test says yes" are premises: the
chain's maker's. S₀, book, tl, L are letters: the verifier's state's own values among them. No
soundness. Nothing on hiding.
-/
import Johnson.P1K8R.OrderAtSeat
import Johnson.Desc.First.K8.LawFenceBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8S

open OnBytes.Maker
open _root_.Run.PQ (CK)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

/-- **THE FENCE AT THE 25 PLACES.** -/
theorem k08_fence {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (hf : Three.Fits T) (file : String)
    (hD : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).data file = .ok D)
    (hP : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true)
    {x : ℕ × ℕ} (hx : x ∈ places) {Xl : LinkH} (hX : Bs.G₀.built[x.1]? = some Xl)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * x.1 + x.2 + 2]? = some q)
    (rad : OnBytes.OracleShape → Nat) (S₀ : OnBytes.Statement) (book : OnBytes.TreeBook)
    (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar S₀ book tl L = true)
    (i : Fin (Named.listOf rad S₀ book tl L).length) :
    (Named.seatFn rad S₀ book tl L i).1 < q.base := by
  obtain ⟨Lk, b, Xl', -, -, hk, hX', -, -, hLike, -⟩ := sitsAt_open hS hR O x hx
  obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
  exact named_seats_below_fits _ file D hD T hT hf hLike hq hk hP rad S₀ book tl L hN i

end P1K8S

#print axioms P1K8S.k08_fence
