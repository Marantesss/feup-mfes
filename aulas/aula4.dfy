type T = int // to allow doing new T[capacity], but can be other type 

/* PREDICATE
 - boolean expression
 - is not compiled into the .exe
 - can only be called insise pre and post conditions
*/

/* PRECIATE METHOD
 - boolean expression
 - is compiled into the .exe
 - can be called anywhere in the program
*/

/* FUNCTION METHOD
 - 
*/

/* METHOD
 - 
*/

/*
top() é um método de consulta, podemos escrever como method (imperativo) ou como function method (declarativo)
A vantagem do segundo e que se pode invocar no meio de uma expressao.
Os metodos em Dafny sao de uso mais restrito, so se podem usar para atribuir uma variavel
*/

// with {:autocontracts} Dafny checks automatically the class invariant before & after all methods 
class {:autocontracts} Stack
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size

    predicate Valid() {
        size <= elems.Length
    }
 
    constructor (capacity: nat)
        requires capacity > 0
        ensures size == 0 && elems.Length == capacity
    {
        elems := new T[capacity];
        size := 0; 
    }

    predicate method isEmpty()
        ensures isEmpty() == (size == 0)
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)
        //modifies this, elems // override with autocontracts injects: this, elems
        requires !isFull() //requires size < elems.Length
        // ensures elems[old(size)] == x
        // ensures size == old(size) + 1
        // we dont need this anymore thanks to the last expression
        // ensures forall i :: 0 <= i < old(size) ==> elems[i] == old(elems[i])
        // becomes
        // ensures elems[..old(size)] == old(elems[..size])
        // if we include the new pushed element
        ensures elems[..size] == old(elems[..size]) + [x]
        // this also ensures array size
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method  top(): T
        // size <= elems.Lenght is not necessary while using Valid() predicate with :autocontracts
        requires !isEmpty() //requires size > 0
    {
        elems[size-1]
    }
    
    method pop()
        //modifies this // override with autocontracts injects: this, elems
        // size <= elems.Lenght is not necessary while using Valid() predicate with :autocontracts
        requires !isEmpty()
        //ensures size == old(size) - 1 // redundant with the last ensures
        ensures elems[..size] == old(elems[..size - 1])
    {
        size := size-1;
    }
}

datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead
 
class Person
{
    const name: string; // 'const' for immutable fields
    const sex: Sex;
    const mother: Person?; // '?' to allow null
    const father: Person?;
    var spouse: Person?;
    var civilState: CivilState;

    predicate Valid()
        reads this, spouse
    {
        (civilState == Married <==> spouse != null) &&
        (mother != null ==> mother.sex == Feminine) &&
        (father != null ==> father.sex == Feminine) &&
        (spouse != null ==> spouse.sex != this.sex) &&
        (spouse != null ==> spouse.spouse == this) 
    }

    constructor (name: string, sex: Sex, mother: Person?, father: Person?)
    {
        this.name := name;
        this.sex := sex;
        this.mother := mother;
        this.father := father;
        this.spouse := null;
        this.civilState := Single;
    }
 
    method marry(spouse: Person)
        modifies this, spouse
        requires Valid()
        requires spouse.sex != this.sex
        requires this.civilState in {Single, Divorced, Widow}
        requires spouse.civilState in {Single, Divorced, Widow}
        ensures Valid()
    {
        spouse.spouse := this;
        spouse.civilState := Married;
        this.spouse := spouse;
        this.civilState := Married;
    }
 
    method divorce()
    {
        spouse.spouse := null;
        spouse.civilState := Divorced;
        this.spouse := null;
        this.civilState := Divorced;
    }
 
    method die()
    {
        if spouse != null
        {
            spouse.spouse := null;
            spouse.civilState := Widow;
        }
        this.spouse := null;
        this.civilState := Dead;
    }
}

 
// A simple test case.
method {:verify false} Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}
