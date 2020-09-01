class Node<T> {
    var next: Node?<T>
    var data: T
    var len: int
    ghost var Rep: set<object>

    constructor (data: T)
        ensures this.data == data
        ensures this.next == null
        ensures fresh(Rep)
        ensures Valid()
    {
        this.data := data;
        this.next := null;
        Rep := {this};
        len := 1;
    }

    predicate Valid() 
        reads this
        reads Rep
        decreases len
    {   
        this in Rep && len > 0 &&
        (next == null ==> Rep == {this} && len == 1) &&
            (next != null ==> next in Rep && next.Rep <= Rep && this !in next.Rep && len == next.len + 1 && next.Valid())
    }
}

class Stack<T> {
    var top: Node?<T>
    var len: int // helps to prove invariants
    ghost var Rep: set<object>

    constructor()
        ensures fresh(Rep)
        ensures top == null
        ensures len == 0
        ensures Valid()
    {   
        this.top := null;
        len := 0;
        Rep := {this};
    }
    
    predicate Valid() 
        reads this
        reads Rep
    {   
        this in Rep && len >= 0 &&
        (top == null ==> Rep == {this} && len == 0) &&
            (top != null ==> top in Rep && top.Rep <= Rep && this !in top.Rep && len == top.len && top.Valid())
    }

    // TODO: add requirement to preserve ordering for all nodes
    method push(data: T)
        requires Valid()
        modifies Rep
        ensures len == old(len) + 1
        ensures top != null && top.data == data
        ensures top.next == old(top) 
        ensures Rep == old(Rep) + {top} // only top element was added to the footprint
        ensures fresh(Rep - old(Rep)) // swinging pivots requirement: any objects added to footprint are newly allocated
        ensures Valid()
    {
        var toAdd := new Node(data);
        toAdd.next := top;
        if (top != null) {
            toAdd.len := toAdd.len + top.len;
        }

        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        top := toAdd;
        Rep := Rep + {top};
        len := len + 1;
        if (top.next == null) {
            top.Rep := {top};
        } else {
            top.Rep := {top} + top.next.Rep;
        }

        // top := null; // correctly raises a verification error: !fresh(top)
        // top.next := new Node(data); // correctly raises a verification error: top.next != old(top)
    } 

    method peek() returns (data: T)
        requires Valid()
        requires top != null
        ensures data == top.data
    {
        data := top.data;
    }

    // TODO: add requirement to preserve ordering for all nodes
    method pop() returns (popped: T) 
        requires Valid()
        requires top != null
        modifies Rep
        ensures len == old(len) - 1
        ensures Rep == old(Rep) - old({top})
        ensures top == old(top.next)
        ensures Valid()
    {
        popped := top.data;
        Rep := Rep - {top};
        top := top.next;
        len := len - 1;
        
        // top := new Node(popped); // correctly raises a verification error: top != old(top.next)
        // top.data := popped; // correctly raises a verification error: may update object not in enclosing context's modifies clause
        // top.next := null; // correctly raises a verification error: may update object not in enclosing context's modifies clause
    }

    method size() returns (s: int)
        requires Valid()
        ensures s == len
        ensures Valid()
    {
        s := len;
    }

    method isEmpty() returns (isEmpty: bool) 
        requires Valid()
        ensures top == null <==> isEmpty
        ensures Valid()
    {
        if top == null {
            isEmpty := true;
        } else {
            isEmpty := false;
        }
    }
}

method Test() {
    var A := new Stack<int>();
    assert A.len == 0;
    var B := new Stack<int>();
    A.push(10);
    assert B.len == 0;
    A.push(10);
    assert B.len == 0;
    assert A.len == 2;
}




   