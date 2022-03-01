Require Import Coq.Unicode.Utf8.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.

Reserved Notation "A ~> B" (at level 80, right associativity).
Reserved Notation "A ∘ B" (at level 30).

Class Category := {
  Obj: Type ;
  Mor: Obj → Obj → Type ;

  Mor_Setoid A B: Setoid (Mor A B) ;

  id A: Mor A A ;
  compose {A B C}: Mor B C -> Mor A B -> Mor A C
  where "f ∘ g" := (compose f g) ;

  compose_assoc {A B C D} (f: Mor C D) (g: Mor B C) (h: Mor A B):
    (f ∘ (g ∘ h)) == ((f ∘ g) ∘ h );
  compose_id_left {A B} (f: Mor A B): (id B ∘ f) == f ;
  compose_id_right {A B} (f: Mor A B): (f ∘ id A) == f ;

  compose_compat {A B C}: Proper (equiv ==> equiv ==> equiv) (@compose A B C) ;
}.

Arguments Obj: clear implicits.
Arguments Mor: clear implicits.

Coercion Obj: Category >-> Sortclass.
Coercion Mor: Category >-> Funclass.

Existing Instance Mor_Setoid.
Existing Instance compose_compat.

Module CategoryNotations.
  Declare Scope category_scope.
  Declare Scope object_scope.
  Declare Scope morphism_scope.

  Delimit Scope category_scope with category.
  Delimit Scope object_scope with object.
  Delimit Scope morphism_scope with morphism.

  Bind Scope category_scope with Category.
  Bind Scope object_scope with Obj.
  Bind Scope morphism_scope with Mor.

  Notation "f ∘ g" := (compose f g) : morphism_scope.
  Notation "A ~> B" := (Mor _ A B) (only parsing) : type_scope.
End CategoryNotations.
