namespace Nemonuri.TypeSystems.FOmega

open Nemonuri.TypeSystems.FOmega.Primitives


module Surfaces = begin

    module K = Kinds
    module C = Canons

    type ISurface<'kind, 'canon 
                    when 'kind :> K.IKind
                    and 'canon :> C.ICanon<'kind>> = interface end
    
    type Star<'a> = struct
        interface ISurface<K.Star, C.Star<'a>>
    end

    type IArrow<'pk, 'pc, 'qk, 'qc, 'qs
                    when 'pk :> K.IKind and 'pc :> C.ICanon<'pk>
                    and 'qk :> K.IKind and 'qc :> C.ICanon<'qk>
                    and 'qs :> ISurface<'qk, 'qc>> = interface
        inherit ISurface<K.Arrow<'pk, 'qk>, C.Arrow<'pk, 'pc, 'qk, 'qc>>

        abstract member Apply: 'pc -> 'qs
    end

    //let toCanon (s: #ISurface<'kind, 'canon>) = Unchecked.defaultof<'canon>


    type App<'pk, 'pc, 'qk, 'qc, 'fn, 'arg
                when 'pk :> K.IKind and 'pc :> C.ICanon<'pk>
                and 'qk :> K.IKind and 'qc :> C.ICanon<'qk>
                and 'fn :> ISurface<K.Arrow<'pk, 'qk>, C.Arrow<'pk, 'pc, 'qk, 'qc>>
                and 'arg :> ISurface<'pk, 'pc>> = struct end

end

