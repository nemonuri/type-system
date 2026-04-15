namespace Nemonuri.TypeSystems.FOmega

open Nemonuri.TypeSystems.FOmega.Primitives
open Nemonuri.TypeSystems.FOmega.Surfaces

module Evaluation = begin

    module K = Kinds
    module C = Canons

    let toCanon (s: #ISurface<'kind, 'canon>) = Unchecked.defaultof<'canon>

    type Star<'a> with

        static member Eval (self: Star<'a>) = self

    end

(*
    type App<'pk, 'pc, 'qk, 'qc, 'fn, 'arg
                when 'pk :> K.IKind and 'pc :> C.ICanon<'pk>
                and 'qk :> K.IKind and 'qc :> C.ICanon<'qk>
                and 'fn :> ISurface<K.Arrow<'pk, 'qk>, C.Arrow<'pk, 'pc, 'qk, 'qc>>
                and 'arg :> ISurface<'pk, 'pc>> with

        static member inline Eval (app: App<'pk, 'pc, 'qk, 'qc, 'fn, 'arg>) =


    end
*)

end