import "ast" as ast
import "errormessages" as errormessages
import "sourcePosition" as sourcePosition

// This module defines "variables": the objects that populate the symbol table.
// Every name declared in a Grace program is bound to one of these "variables",
// so methods, types, parameters, and imported modules are all "variables" in
// this sense.  

// Type variables also double as type objects for type checking; this is 
// probably wrong, and has been commented out.

var moduleRegistry

type Scope = Unknown

type Variable = interface {
    canBeOrginOfSuperExpression → Boolean
    declaredName → String
    definingParseNode → ast.AstNode
    definingScope → Scope
    isAnnotatedConfidential → Boolean
    isAnnotatedPublic → Boolean
    isAnnotatedReadable → Boolean
    isAnnotatedWith (anAnnotationName) → Boolean
    isAnnotatedWritable → Boolean
    isAssignable → Boolean
    isAvailableForReuse → Boolean
    isConcrete → Boolean
    isConfidential → Boolean
    isExplicitMethod → Boolean
    isIfThenElse → Boolean
    isImport → Boolean
    isMatchCase → Boolean
    isMethod → Boolean
    isMethodOrParameterizedType → Boolean
    isOnceMethod → Boolean
    isPublic → Boolean
    isPublicByDefault → Boolean
    isReadable → Boolean
    isSpecialControlStructure → Boolean
    isTryCatch → Boolean
    isType → Boolean
    isTypeParameter → Boolean
    isWritable → Boolean
    kind → String
    lineRangeString → String
    moduleName → String
    range → sourcePosition.Range
    rangeLongString → String
    rangeString → Boolean
    startPosition → sourcePosition.Position
    stopPosition → sourcePosition.Position
}
    

class graceDefFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe the variable defined in a def declaration.

    method canBeOrginOfSuperExpression {
        definingParseNode.parent.isModule
    }
    once method isPublic {
        isAnnotatedPublic || { isAnnotatedReadable }
    }
    method == (anotherType) {
        (self == anotherType )
    }
    method asString {
        "def "++ name
    }
    once method attributeScope {
        definingParseNode.initializer.scope
    }
    method kind { "def" }
}

class graceImportFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe the "nickname" variable defined in an import declaration.

    method canBeOrginOfSuperExpression {
        true
    }
    once method isPublic {
        isAnnotatedPublic || { isAnnotatedReadable }
    }
    method isAvailableForReuse {
        false
    }
    method canBeOverridden {
        false
    }
    method asString {
        "import " ++ name
    }
    once method attributeScope {
        moduleRegistry.attributeScopeOf (definingParseNode.resourceValue)
    }
    method isImport {
        true
    }
    method kind { "import" }
}
class graceMethodFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe a method defined in a method declaration.

    method isPublicByDefault {
        true
    }
    method substitute (bindings) {
        self.shouldBeImplemented
    }
    method isMethodOrParameterizedType {
        true
    }
    method asString {
        "meth " ++ name
    }
    once method attributeScope {
        definingParseNode.attributeScope
    }
    method isExplicitMethod {
        true
    }
    method returns {
        definingParseNode.returns
    }
    once method isOnceMethod {
        definingParseNode.isOnceMethod
    }
    method parameters {
        definingParseNode.header.parameters
    }
//    method join (anotherMethod) {
//        def result = graceImplicitSignatureFrom(ast.nullNode)
//        return result
//    }
    method isMethod { true }
    method kind { "method" }
}
class graceParameterFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe the paramter to  a method or block.

    method isAvailableForReuse {
        false
    }
    method asString {
        "param " ++ name
    }
    method kind { "parameter" }
}
class gracePseudovariableFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I represent the pseudoVariable self, or the pseudovariable outer, or outer.outer, or outer.outer.outer ...
    // isModule:  true if the object that I refer to is a module object
    // isDialect: true if the object that I refer to is a dialect object
    // elementScope: the scope defined by the object to which I refer
    

    def isModule is public = node.isModule
    def isDialect is public = node.isDialect

    method isAvailableForReuse { false }
    method name {
        name.ifNotNil {
            return name
        }
        if (isModule) then {
            return "the module"
        }
        if (isDialect) then {
            return "the dialect"
        }
        return "an Object"
    }
    method canBeOverridden {
        // the object associated with self or outer... is not subject to overriding
        return false
    }
    method asString {
        "psdVar for " ++ name
    }
    method returns { definingParseNode.returns }
    method kind { "pseudo-variable" }
}
class graceTypeFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe the type name defined in a type declaration.
    // instance variables:
    // typeValue --- once type objects have been created, a type object representing me.
    // It will be a subinstance of graceAbstractType

    method typeName { name }
//    method methodNamed (aName) {
//        methodNamed (aName) ifAbsent {
//            errormessages.error "the type {name} does not have a method {aName}"
//        }
//    }
    method isPublicByDefault { true }
    method isType { true }
//    method substitute (bindings) {
//        return self
//    }
    method isMethodOrParameterizedType {
        return (numberOfParameters > 0)
    }
//    method methodNamesAndSignaturesDo (a2ArgBlock) {
//        attributeScope.localNamesAndValuesDo { n, v →
//            def sig = graceSignatureOfMethod (v)
//            a2ArgBlock.value (n) value (sig)
//        }
//   }
    method isSelfType { false }
    method asString {
        var result := "type " ++ name
        if (hasParameters) then {
            result := result ++ "⟦"
            parameters.do { each →
                result := result ++ each.name
            } separatedBy {
                result := result ++  ", "
            }
            result := result ++ "⟧"
        }
        result
    }
//    method methodNames {
//        typeValue.methodNames
//    }
    once method attributeScope {
        // the scope for the attributes of this type
        definingParseNode.value.attributeScope
    }
//    once method typeValue {
//        // typeValue unwinds this type definition exactly once.  Any references into this variable in
//        // the resulting type are NOT replaced by the type that they name, since this would lead to infinite
//        // regress.
//        graceBuildType.from (definingParseNode.value) typeName (name)
//    }
    method numberOfParameters { definingParseNode.numberOfTypeParameters }
    method parameters { definingParseNode.typeParameters.parameters }
//    method conformsTo (aGraceType) underAssumptions (assumptions) {
//        return typeValue.conformsTo (aGraceType) underAssumptions (assumptions)
//    }
//    method isUnknown {
//        return typeValue.isUnknown
//    }
//    method conformsTo (aGraceType) {
//        return typeValue.conformsTo (aGraceType)
//    }
    method isPublic { true }
//    method conformsTo (anotherType) inType (selfType) underAssumptions (assumptions) {
//        return typeValue.conformsTo (anotherType) inType (selfType) underAssumptions (assumptions)
//    }
//    method variants {
//        // this method was not complete in the Smalltalk code
//        def val = definingParseNode.value
//        if (val.isInterface) then {
//            [ self ]
//        } else {
//            buildTypeFrom(val).variants
//        }
//    }
//    method instantiateWithArgs (aCollectionOfTypes) {
//        def instance = graceTypeInstance.newFrom (self) withArguments (aCollectionOfTypes)
//        return instance
//    }
//    method methodNamed (aString) ifAbsent (aBlockClosure) {
//        return typeValue.methodNamed (aString) ifAbsent (aBlockClosure)
//    }
    method checkNumberOfTypeArguments (aType) {
        if ((aType.numberOfArguments == numberOfParameters).not) then {
            errormessages.syntaxError.
                  raise "type {typeName} needs {numberOfParameters} arguments, but given {aType.numberOfArguments}" 
                  with (aType)
        }
    }
//    method isVariant {
//        return typeValue.isVariant
//    }
//    method typeValue (aTypeObject) {
//        // sets the typeValue field to aTypeObject, and returns aTypeObject.  
//        // Makes the aTypeObject aware that it now has a name
//        aTypeObject.typeName (typeName)
//        typeValue := aTypeObject
//        aTypeObject
//    }
    method hasParameters {
        return (numberOfParameters > 0)
    }
    method kind { "type" }
}
class graceTypeParameterFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe a type parameter to a type or method.

    method hash {
        // == has been overriden to be identity
        myIdentityHash
    }
//    method conformsTo (anotherType) inType (selfType) underAssumptions (assumptions) {
//        return anotherType.isTypeParameter
//    }
    method == (other) {
        // is other the same parameter as me?
        self.isMe (other)
    }
    method isAvailableForReuse { false }
    method isType { true }
    method variants {
        return [ self ]
    }
//    method substitute (bindings) {
//        // bindings maps type parameters to argument values
//        def argValue = bindings.at (self) ifAbsent {
//            return self
//        }
//        halt
//        return argValue
//    }
    method isTypeParameter { true }
    method asString {
        "typeParam " ++ name
    }
    method kind { "type parameter" }
}
class graceVarFrom (node) {
    inherit graceAbstractVariableFrom (node)
    // I describe the variable defined in a var declaration.

    method isAssignable { true }
    method asString {
        "var " ++ name
    }
    method isWritable { isPublic || { isAnnotatedWritable } }
    method isConfidential { isReadable.not && { isWritable.not } }
    method kind { "var" }
}
class graceImplicitMethodFrom (node) {
    inherit graceMethodFrom (node)
    // I represent a writer method implicitly declared by a var declaration

    method isPublic { false }
    method asString { "implicitMeth " ++ name }
    method isExplicitMethod { false }
    method kind { "var" }
}
class graceRequiredMethodFrom (node) {
    inherit graceMethodFrom (node)
    // A required method is one that has no body, but serves as a marker that the 
    // programmer should provide a real method.   Required methods never override 
    // real methods, even if the required method comes from a trait and the real 
    // method comes from a superobject.

    method isPublic { false }
    method isConcrete { false }
    method kind { "required method" }
}
class graceSpecialControlStructureFrom (node) withName (aMethodName) {
    inherit graceMethodFrom (node)
    // I represent a method implicitly declared for one of the special control structures.
    // These are (using regular expression notation and omitting argument lists):
    // - if then ( elseif then )* else?
    // - match case+
    // - try catch * finally?
    
    name := aMethodName
    method isSpecialControlStructure { true }
    method asString { "ctrl " ++ name }
    method kind { "method" }
    method isTryCatch { name.startsWith "try" }
    method isIfThenElse { name.startsWith "if" }
    method isMatchCase { name.startsWith "match" }
}
//class graceImplicitSignatureFrom (node) {
//    inherit graceMethodFrom (node)
//    // I represent a signature created implicitly while calculating the meet and join of other signatures.
//
//    method initializeAsJoinOf (methA) and (methB) {
//        name := methA.declaredName
//        argumentTypes := methA.arguments.with (methB.arguments) collect { a, b →
//            a.declaredType.meet (b.declaredType)
//        }
//        resultType := methA.result.declaredType.join (methB.result.declaredType)
//    }
//}
//class graceTypeInstanceFrom (aGraceType) withArguments (typeArgs) {
//    inherit graceTypeFrom (aGraceType.definingParseNode)
//    // I represent a graceType that has been instantiated with type arguments.
//    // Instance variables:
//    // arguments – a list of type arguments, with size self.numberOfParameters.
//    
//    
//    attributeScope := aGraceType.attributeScope
//    definingAstNode := aGraceType.definingAstNode
//    isAnnotation := aGraceType.isAnnotation
//    isMarker := aGraceType.isMarker
//    isPublic := aGraceType.isPublic
//    name := aGraceType.name
//    arguments := typeArgs
//
//    method substituteForParametersIn (aSignature) {
//        def bindings = Dictionary.new
//        parameters.with (arguments) do { param, val →
//            bindings.at (param.variable) put (val)
//        }
//        return aSignature.substitute (bindings)
//    }
//    method arguments {
//        return arguments
//    }
//    
//    method substitute (bindings) {
//        arguments.doWithIndex { each, i →
//            bindings.at (each) ifAbsent {
//            } ifPresent { val →
//                arguments.at (i) put (val)
//            }
//        }
//    }
//    method parameters {
//        return definingParseNode.typeParameters.parameters
//    }
//}
class graceAbstractVariable {
    
    // The superclass of classes that describe the various kinds of variable
    // in a Grace program.
    // The common interface lets clients make the following requests
    //   isAssignable  — true for vars only
    //   isType — true for types only
    //   isMethod — true for methods, both implicit & explicit
    //   isExplicitMethod — true for expliict methods only
    //   kind — a string ('var', 'def', 'method', 'parameter' etc.)
    //   definingNode — the parse tree node that defines this variable
    //   range — the source-code range of my declaration
    //   startPosition — the start of the range
    //   stopPosition  — the end of the range
    //   attributeScope — characterizes the attributes of the  object bound
    //      to this variable.  For example, if I am a def bound to an object j,
    //      then attributeScope describes the attibutes of j.
    
    var name is public
    var declaredType is public
    var definingAstNode is public
    var attributeScope is public 
    var isMarker is readable
    var isAnnotation is public
    var definingParseNode is readable
    var isModule is readable := false
    var isDialect is readable := false
    
    method stopPosition { definingParseNode.stopPosition }
    method canBeOrginOfSuperExpression { false }
    method isPublicByDefault { false }
    method isAvailableForReuse { true }
    method isAnnotatedReadable {
        return isAnnotatedWith "readable"
    }
    method isType { false }
    method isConcrete { true }
    method isMethodOrParameterizedType { false }
    method kind is abstract
    method isAnnotatedConfidential {
        return isAnnotatedWith "confidential"
    }
    method isWritable { false }
    method isExplicitMethod { false }
    method definingScope { definingParseNode.scope }
    method isImport { false }
    method isOnceMethod { false }
    method rangeLongString { range.rangeLongString }
    method declaredName { name }
    method isAnnotatedWith (anAnnotationName) {
        definingParseNode.annotationNames.includes (anAnnotationName)
    }
    method isSpecialControlStructure { false }
    method isAssignable { false }
    method range { definingParseNode.range }
    method isAnnotatedWritable { isAnnotatedWith "writable" }
    once method isPublic {
        isAnnotatedPublic || { isAnnotatedConfidential.not && isPublicByDefault }
    }
    method startPosition { definingParseNode.startPosition }
    method lineRangeString { range.lineRangeString }
    method isReadable { isPublic || { isAnnotatedReadable } }
    method rangeString { range.rangeString }
    method isTypeParameter { false }
    method isConfidential { isPublic.not }
    method isAnnotatedPublic { isAnnotatedWith "public" }
    method isMethod { false }
    method isTryCatch { false }
    method isIfThenElse { false }
    method isMatchCase { false }
    method moduleName { definingParseNode.moduleName }
}

class graceAbstractVariableFrom (aDeclarationNode) {
    inherit graceAbstractVariable

    name := aDeclarationNode.nameString
    declaredType := aDeclarationNode.dtype
    isMarker := aDeclarationNode.isMarkerDeclaration
    isAnnotation := aDeclarationNode.hasAnnotation "annotation"
    definingParseNode := aDeclarationNode
}

class named (aName) typed (dType) kind (aKind) {
    // defines a variable that does not have a parse node, as when
    // the variable is imported from another module.
    inherit graceAbstractVariable

    name := aName
    declaredType := dType
    isAnnotation := false
    isMarker := false
    definingParseNode := ast.nullNode
    def kind is public = "imported {aKind}"
    def asString is public = "a variable named {aName} typed {dType} kind {aKind}"
}

class named (aName) typed (dType) kind (aKind) attributeScope (s) {
    inherit named (aName) typed (dType) kind (aKind)
    attributeScope := s
}
