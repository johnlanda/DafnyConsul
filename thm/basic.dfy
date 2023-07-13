include "../core/all.dfy"

module basic {
    import opened def.base
    import opened def.core
    import opened def.engine

    lemma DenyTrumpsAllowOfSamePrecendence(request: Request, store: Store)
      requires // A max precedence deny policy exists
        exists i ::
          i in store.intentions.intentions.Keys &&
          store.intentions.intentions[i].action == Deny &&
          i in Authorizer(request, store).satisfiedMaxPrecedenceIntentions()
      ensures // The request is denied
        Authorizer(request, store).isAuthorized().decision == DenyRequest
      {
        var d :| d in Authorizer(request, store).denies();
      }

      // Not how consul is really set up but
      // its coded into dafny as the defaul for now.
      lemma DefaultDeny(request: Request, store: Store)
        ensures // if not explicitly permitted, a request is denied
         (!exists i ::
           i in store.intentions.intentions.Keys && Authorizer(request, store).satisfied(i)) ==>
           Authorizer(request, store).isAuthorized().decision == DenyRequest
      {}

      lemma HigherPrecedenceAllowTrumpsLowerDeny(request: Request, store: Store)
        requires // a higher max precedence allow policy exists
          exists a ::
            a in store.intentions.intentions.Keys &&
            store.intentions.intentions[a].action == Allow &&
            a in Authorizer(request, store).satisfiedMaxPrecedenceIntentions()
        requires // a max precedence deny does not exist
          !exists d ::
            d in store.intentions.intentions.Keys &&
            store.intentions.intentions[d].action == Deny &&
            d in Authorizer(request, store).satisfiedMaxPrecedenceIntentions()
        requires // a lower precedence deny exists
          exists d ::
            d in store.intentions.intentions.Keys &&
            store.intentions.intentions[d].action == Deny &&
            d !in Authorizer(request, store).satisfiedMaxPrecedenceIntentions()
        ensures // the request is allowed
          Authorizer(request, store).isAuthorized().decision == AllowRequest
        {
          var a :| a in Authorizer(request, store).allows();
        }
}