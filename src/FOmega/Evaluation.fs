namespace Nemonuri.TypeSystems.FOmega

open Nemonuri.TypeSystems.FOmega.Primitives
open Nemonuri.TypeSystems.FOmega.Surfaces
module K = Kinds
module C = Canons

module Evaluation = begin

    let inline apply<'pk, 'pc, 'qk, 'qc, 'qs, 'fn
                        when 'pk :> K.IKind and 'pc :> C.ICanon<'pk>
                        and 'qk :> K.IKind and 'qc :> C.ICanon<'qk>
                        and 'qs :> ISurface<'qk, 'qc>
                        and 'fn :> ISurface<K.Arrow<'pk, 'qk>, C.Arrow<'pk, 'pc, 'qk, 'qc>>
                        and ('fn or 'pc) : (static member Apply: 'pc -> 'qs)> 
                (pc: 'pc) =
        ((^fn or ^pc) : (static member Apply: 'pc -> 'qs) pc) 

    let inline eval<'k, 'c, 's, 'r, 'p
                        when 'k :> K.IKind
                        and 'c :> C.ICanon<'k>
                        and 's :> ISurface<'k, 'c>
                        and 'p : (static member Eval: 's -> 'r)>
                (s: 's) =
        'p.Eval s

    let toCanon (s: #ISurface<'kind, 'canon>) = Unchecked.defaultof<'canon>

    type Premise = struct

        static member Eval (star: Star<'a>) = star

        static member inline Eval (app: App<'pk, 'pc, 'qk, 'qc, 'fn, 'arg>) =
            apply<'pk, 'pc, 'qk, 'qc, 'qs, 'fn> (toCanon Unchecked.defaultof<'arg>)

    end





end