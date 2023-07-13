include "base.dfy"
include "core.dfy"

module def.engine {
    import opened base
    import opened core

    datatype Authorizer = Authorizer(request: Request, store: Store) {

        function evaluator(): Evaluator {
            Evaluator(request, store.entities)
        }
        
        function evaluate(intentionID: IntentionID): Result<Value> 
        requires intentionID in store.intentions.intentions
        {
            evaluator().interpret(store.intentions.intentions[intentionID].toExpr())
        }

        predicate satisfied(intentionID: IntentionID)
        requires intentionID in store.intentions.intentions
        {
            evaluate(intentionID) == Ok(Value.TRUE)
        }

        function satisfiedIntentions(): set<IntentionID> {
            set iid | iid in store.intentions.intentions.Keys && satisfied(iid)
        }

        function satisfiedMaxPrecedenceIntentions(): set<IntentionID> {
            set iid | iid in satisfiedIntentions() && 
                forall x :: x in satisfiedIntentions() ==> store.intentions.intentions[x].precedence <= store.intentions.intentions[iid].precedence
        }

        function allows(): set<IntentionID> {
            set iid | iid in satisfiedMaxPrecedenceIntentions() && store.intentions.intentions[iid].action == Allow
        }

        function denies(): set<IntentionID> {
            set iid | iid in satisfiedMaxPrecedenceIntentions() && store.intentions.intentions[iid].action == Deny
        }

        function isAuthorized(): Response {
            var d := denies();
            var a := allows();

            // assert that we have only policies of one precedence
            // 1. all denies same precedence
            assert forall x, y :: x in d && y in d ==> store.intentions.intentions[x].precedence == store.intentions.intentions[y].precedence;
            // 2. all allows same precedence
            assert forall x, y :: x in a && y in a ==> store.intentions.intentions[x].precedence == store.intentions.intentions[y].precedence;
            // 3. denies and allows are same precedence
            assert forall x, y :: x in a && y in d ==> store.intentions.intentions[x].precedence == store.intentions.intentions[y].precedence;

            // if no denies at max precedence and some allows
            // then allow the request
            if d == {} && a != {} then
                Response(AllowRequest)
            // if any denied intentions at max precedence
            // then deny the request
            else if d != {} then
                Response(DenyRequest)
            // Otherwise both are empty and we can enforce the 
            // default (which we can pretend is set to deny for now)
            else
                Response(DenyRequest)
        }
    }

    datatype Evaluator = Evaluator(request: Request, store: EntityStore) {
        
        function interpret(expr: Expr): Result<Value> {
            match expr {
                case PrimitiveLit(p) => Ok(Primitive(p))
                case Var(v) => 
                    match v {
                        case Source => Ok(Value.EntityUID(request.source))
                        case SourceNamespace => Ok(Value.EntityUID(request.sourceNamespace))
                        case Destination => Ok(Value.EntityUID(request.destination))
                        case DestinationNamespace => Ok(Value.EntityUID(request.destinationNamespace))
                    }
                case And(left, right) =>
                    interpretShortcircuit(expr, left, right, false)
                case BinaryApp(op, e1, e2) =>
                    var v1 :- interpret(e1);
                    var v2 :- interpret(e2);
                    applyBinaryOp(op, v1, v2)
                case Record(es) =>
                    var fvs :- interpretRecord(es);
                    Ok(Value.Record(fvs))
            }
        }

        function interpretRecord(es: seq<(Attr,Expr)>): Result<map<Attr, Value>> {
            if es == [] then
                Ok(map[])
            else
                var k := es[0].0;
                var v :- interpret(es[0].1);
                var m :- interpretRecord(es[1..]);

                if k in m.Keys then // If the same field is repeated later in the record,
                    Ok(m)             // we give that occurrence priority and ignore this one.
                else
                    Ok(m[k := v])
        }

        function interpretShortcircuit(ghost expr: Expr, left: Expr, right: Expr, short: bool): Result<Value>
            requires left < expr && right < expr
        {
            var l :- interpret(left);
            var b :- Value.asBool(l);

            if b == short then Ok(l)
            else
                var r :- interpret(right);
                var _ :- Value.asBool(r);
                Ok(r)
        }

        function applyBinaryOp(bop: BinaryOp, x: Value, y: Value): Result<Value> {
            match bop {
                case Eq =>     Ok(Value.Bool(x == y))
            }
        }
    }
}