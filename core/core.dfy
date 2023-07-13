include "base.dfy"

module def.core {
    import opened base

    datatype PatElem = Star | JustChar(char)

    type Pattern = seq<PatElem>

    type EntityUID = string

    datatype Primitive =
        Bool(b: bool) |
        Int(i:int) |
        String(s: string) |
        EntityUID(s: EntityUID)

    datatype Value =
        Primitive(primitive: Primitive) |
        Set(s: set<Value>) |
        Record(record: Record)
    {
        static function Bool(b: bool): Value {
            Primitive(Primitive.Bool(b))
        }
        static const TRUE := Bool(true)
        static const FALSE := Bool(false)

        static function Int(i: int): Value {
            Primitive(Primitive.Int(i))
        }

        static function String(s: string): Value {
            Primitive(Primitive.String(s))
        }

        static function EntityUID(uid: EntityUID): Value {
            Primitive(Primitive.EntityUID(uid))
        }

        static function asBool(v: Value): Result<bool> {
            match v {
                case Primitive(Bool(b)) => Ok(b)
                case _ => Err(TypeError)
            }
        }

        static function asEntity(v: Value): Result<EntityUID> {
            match v {
                case Primitive(EntityUID(e)) => Ok(e)
                case _ => Err(TypeError)
            }
        }

        static function asSet(v: Value): Result<set<Value>> {
            match v {
                case Set(s) => Ok(s)
                case _ => Err(TypeError)
            }
        }

        static function asRecord(v: Value): Result<Record> {
            match v {
                case Record(r) => Ok(r)
                case _ => Err(TypeError)
            }
        }
    }

    type Attr = string
    type Record = map<Attr, Value>

    datatype Var = Source | SourceNamespace | Destination | DestinationNamespace

    datatype BinaryOp = Eq

    datatype Expr =
        PrimitiveLit(Primitive) |
        Var(Var) |
        And(Expr, Expr) |
        BinaryApp(BinaryOp, Expr, Expr) |
        Record(fvs: seq<(Attr, Expr)>)

    datatype Action = Allow | Deny
    
    datatype IntentionID = IntentionID(id: string)

    // flattened intention representation which
    // maps the consul Intention model to 
    // on dafny Intention per nested source.
    //
    // TODO: require scopes not built on empty string
    datatype Intention = Intention(
        action: Action,
        sourceScope: SourceScope,
        sourceNamespaceScope: SourceNamespaceScope,
        destinationScope: DestinationScope,
        destinationNamespaceScope: DestinationNamespaceScope,
        precedence: int)
    {
        function toExpr(): Expr {
            Expr.And(
                sourceScope.toExpr(),
                Expr.And(
                    sourceNamespaceScope.toExpr(),
                    Expr.And(
                        destinationScope.toExpr(),
                        destinationNamespaceScope.toExpr()
                    )
                )
            )
        }
    }

    /*
     * From: https://developer.hashicorp.com/consul/docs/connect/intentions#precedence-and-match-order
     *
     *  ----------------------------------------------------------------------------------------
     * | Precedence | Source Namespace | Source Name | Destination Namespace | Destination Name |
     *  ----------------------------------------------------------------------------------------
     * | 9          | Exact            | Exact       | Exact                 | Exact            |
     * | 8          | Exact            | *           | Exact                 | Exact            |
     * | 7          | *                | *           | Exact                 | Exact            |
     * | 6          | Exact            | Exact       | Exact                 | *                |
     * | 5          | Exact            | *           | Exact                 | *                |
     * | 4          | *                | *           | Exact                 | *                |
     * | 3          | Exact            | Exact       | *                     | *                |
     * | 2          | Exact            | *           | *                     | *                |
     * | 1          | *                | *           | *                     | *                |
     *  ----------------------------------------------------------------------------------------
     */
    function Precedence(i: Intention): int 
      ensures 0 < Precedence(i) <= 9 
    {
        // I am sure there is a cleaner way to do this 
        // but this clearly matches the table for now 
        // so it is a good reference to show we actually 
        // implement the docs.
        if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope != SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope != DestinationScope(Scope.Any) then 9
        else if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope != DestinationScope(Scope.Any) then 8
        else if i.sourceNamespaceScope == SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope != DestinationScope(Scope.Any) then 7
        else if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope != SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope == DestinationScope(Scope.Any) then 6
        else if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope == DestinationScope(Scope.Any) then 5
        else if i.sourceNamespaceScope == SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
            i.destinationNamespaceScope != DestinationNamespaceScope(Scope.Any) && i.destinationScope == DestinationScope(Scope.Any) then 4
        else if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope != SourceScope(Scope.Any) &&
            i.destinationNamespaceScope == DestinationNamespaceScope(Scope.Any) && i.destinationScope == DestinationScope(Scope.Any) then 3
        else if i.sourceNamespaceScope != SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
            i.destinationNamespaceScope == DestinationNamespaceScope(Scope.Any) && i.destinationScope == DestinationScope(Scope.Any) then 2
        //else if i.sourceNamespaceScope == SourceNamespaceScope(Scope.Any) && i.sourceScope == SourceScope(Scope.Any) &&
        //    i.destinationNamespaceScope == DestinationNamespaceScope(Source.Any) && i.destinationScope == DestinationScope(Scope.Any) then 1
        else 1

    }

    datatype SourceScope = SourceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.Source)
        }
    }

    datatype SourceNamespaceScope = SourceNamespaceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.SourceNamespace)
        }
    }

    datatype DestinationScope = DestinationScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.Destination)
        }
    }

    datatype DestinationNamespaceScope = DestinationNamespaceScope(scope: Scope)
    {
        function toExpr(): Expr {
            scope.toExpr(Var.DestinationNamespace)
        }
    }

    datatype Scope = Any | Eq(entityUID: EntityUID)
    {
        function toExpr(v: Var): Expr {
            match this {
                // Since we do not allow partial matches we can check for
                // just the Any (*) case or the exact match
                case Any => PrimitiveLit(Primitive.Bool(true))
                case Eq(e) => BinaryApp(BinaryOp.Eq, Var(v), PrimitiveLit(Primitive.EntityUID(e)))
            }
        }
    }

    datatype Request = 
        Request(source: EntityUID,
                sourceNamespace: EntityUID,
                destination: EntityUID,
                destinationNamespace: EntityUID)

    datatype EntityData = EntityData(attrs: Record)

    datatype EntityStore = EntityStore(
        entities: map<EntityUID, EntityData>)
    {
        function getEntity(uid: EntityUID): base.Result<Record> {
            if uid in entities.Keys then
                Ok(entities[uid].attrs)
            else
                Err(EntityDoesNotExist)
        }
    }

    datatype IntentionStore = IntentionStore(intentions: map<IntentionID, Intention>)

    datatype Store = Store(entities: EntityStore, intentions: IntentionStore)
    
    datatype Response = Response(decision: Decision)

    datatype Decision = AllowRequest | DenyRequest
}