package play.classloading.enhancers;

import java.io.File;
import java.util.Arrays;
import java.util.Stack;

import javassist.CtBehavior;
import javassist.CtClass;
import javassist.CtField;
import javassist.Modifier;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.Bytecode;
import javassist.bytecode.CodeAttribute;
import javassist.compiler.CompileError;
import javassist.compiler.Javac;
import bytecodeparser.analysis.decoders.DecodedMethodInvocationOp;
import bytecodeparser.analysis.decoders.DecodedMethodInvocationOp.MethodParams;
import bytecodeparser.analysis.opcodes.ExitOpcode;
import bytecodeparser.analysis.stack.StackAnalyzer;
import bytecodeparser.analysis.stack.StackAnalyzer.Frame;
import bytecodeparser.analysis.stack.StackAnalyzer.Frames;
import bytecodeparser.analysis.stack.StackAnalyzer.Frames.FrameIterator;
import bytecodeparser.utils.Utils;
import play.Logger;
import play.Play;
import play.classloading.ApplicationClasses.ApplicationClass;
import play.exceptions.UnexpectedException;
import play.libs.Codec;

public class LVEnhancer extends Enhancer {
    @Override
    public void enhanceThisClass(ApplicationClass applicationClass)
            throws Exception {
        CtClass ctClass = makeClass(applicationClass);
        if(ctClass.isAnnotation() || ctClass.isInterface())
            return;
        for(CtBehavior behavior : ctClass.getDeclaredMethods()) {
            try {
                /*if(ctClass.getName().equals("controllers.Application")) {
                    System.out.println("declared method " + behavior.getLongName());
                }*/
                if(behavior.isEmpty() || behavior.getMethodInfo().getCodeAttribute() == null || Utils.getLocalVariableAttribute(behavior) == null) {
                    //System.out.println("declared empty method " + behavior.getLongName() + " (" + Modifier.toString(behavior.getModifiers()) +")");
                    CtField signature = CtField.make("public static String[] $" + behavior.getName() + "0 = new String[0];", ctClass);
                        //System.out.println("\n\nBEWARE\npublic static String[] $" + behavior.getName() + "0 = new String[0]; in " + ctClass.getName());
                    ctClass.addField(signature);
                    continue;
                }

                StackAnalyzer parser = new StackAnalyzer(behavior);

                // first, compute hash for parameter names
                CtClass[] signatureTypes = behavior.getParameterTypes();
                int memberShift = Modifier.isStatic(behavior.getModifiers()) ? 0 : 1;

                if(signatureTypes.length > parser.context.localVariables.size() - memberShift) {
                    Logger.debug("ignoring method: %s %s (local vars numbers differs : %s != %s)", Modifier.toString(behavior.getModifiers()), behavior.getLongName(), signatureTypes.length, parser.context.localVariables.size() - memberShift);
                    continue;
                }

                StringBuffer signatureNames;
                if(signatureTypes.length == 0)
                    signatureNames = new StringBuffer("new String[0];");
                else {
                    signatureNames = new StringBuffer("new String[] {");

                    for(int i = memberShift; i < signatureTypes.length + memberShift; i++) {
                        if(i > memberShift)
                            signatureNames.append(",");

                        signatureNames.append("\"").append(parser.context.localVariables.get(i).name).append("\"");
                    }
                    signatureNames.append("};");
                }

                CtField signature = CtField.make("public static String[] $" + behavior.getName() + computeMethodHash(signatureTypes) + " = " + signatureNames.toString(), ctClass);
                /*if(ctClass.getName().equals("controllers.Application")) {
                    System.out.println("public static String[] $" + behavior.getName() + computeMethodHash(signatureTypes) + " = " + signatureNames.toString() + " is now " + Modifier.toString(signature.getModifiers()));
                }*/
                ctClass.addField(signature);
                // end

                Frames frames = parser.analyze();
                CodeAttribute codeAttribute = behavior.getMethodInfo().getCodeAttribute();
                FrameIterator iterator = frames.iterator();
                while(iterator.hasNext()) {
                    Frame frame = iterator.next();
                    if(!frame.isAccessible) {
                        Logger.debug("WARNING : frame " + frame.index + " is NOT accessible");
                        continue;
                    }
                    if(frame.decodedOp instanceof DecodedMethodInvocationOp) {
                        DecodedMethodInvocationOp dmio = (DecodedMethodInvocationOp) frame.decodedOp;
                        //StringBuffer stmt = new StringBuffer("{");
                        MethodParams methodParams = DecodedMethodInvocationOp.resolveParameters(frame);
                        
                        String[] paramsNames = new String[methodParams.params.length + (methodParams.varargs != null ? methodParams.varargs.length : 0)];
                        for(int i = 0; i < methodParams.params.length; i++)
                            if(methodParams.params[i] != null && methodParams.params[i].name != null)
                                paramsNames[i] = methodParams.params[i].name;
                        if(methodParams.varargs != null)
                            for(int i = 0, j = methodParams.params.length; i < methodParams.varargs.length; i++, j++)
                                if(methodParams.varargs[i] != null && methodParams.varargs[i].name != null)
                                    paramsNames[j] = methodParams.varargs[i].name;
                        
                        /*stmt.append("String[] $$paramNames = new String[").append(methodParams.params.length + (methodParams.varargs != null ? methodParams.varargs.length : 0)).append("];");
                        for(int i = 0; i < methodParams.params.length; i++)
                            if(methodParams.params[i] != null && methodParams.params[i].name != null)
                                stmt.append("$$paramNames[").append(i).append("] = \"").append(methodParams.params[i].name).append("\";");
                        if(methodParams.varargs != null)
                            for(int i = 0, j = methodParams.params.length; i < methodParams.varargs.length; i++, j++)
                                if(methodParams.varargs[i] != null && methodParams.varargs[i].name != null)
                                    stmt.append("$$paramNames[").append(j).append("] = \"").append(methodParams.varargs[i].name).append("\";");*/

                        Bytecode b = makeInitMethodCall(behavior, dmio.getName(), dmio.getNbParameters(), methodParams.subject != null ? methodParams.subject.name : null, paramsNames);
                        insert(b, ctClass, behavior, codeAttribute, iterator, frame, false);
                        /*stmt.append("play.classloading.enhancers.LVEnhancer.LVEnhancerRuntime.initMethodCall(\"" + dmio.getName() + "\", " + dmio.getNbParameters() + ", " + (methodParams.subject != null ? ("\"" + methodParams.subject + "\"") : "null") + ", $$paramNames);");
                        stmt.append("}");

                        insert(stmt.toString(), ctClass, behavior, codeAttribute, iterator, frame, false);*/
                    }
                    if(frame.decodedOp.op instanceof ExitOpcode) {
                        Bytecode b = makeExitMethod(behavior, ctClass.getName(), behavior.getName(), behavior.getSignature());
                        insert(b, ctClass, behavior, codeAttribute, iterator, frame, false);
                        //insert("play.classloading.enhancers.LVEnhancer.LVEnhancerRuntime.exitMethod(\""+ ctClass.getName() + "\", \"" + behavior.getName() + "\", \"" + behavior.getSignature() + "\");", ctClass, behavior, codeAttribute, iterator, frame, false);
                    }
                    if(iterator.isFirst()) {
                        insert(makeEnterMethod(behavior, ctClass.getName(), behavior.getName(), behavior.getSignature()), ctClass, behavior, codeAttribute, iterator, frame, false);
                        //insert("play.classloading.enhancers.LVEnhancer.LVEnhancerRuntime.enterMethod(\""+ ctClass.getName() + "\", \"" + behavior.getName() + "\", \"" + behavior.getSignature() + "\");", ctClass, behavior, codeAttribute, iterator, frame, false);
                    }
                }
            } catch(Exception e) {
                throw new UnexpectedException("LVEnhancer: cannot enhance the behavior '" + behavior.getLongName() + "'", e);
            }
        }
        applicationClass.enhancedByteCode = ctClass.toBytecode();
        ctClass.defrost();
    }
    
    private static final long startedAt = System.currentTimeMillis();
    
    private static Bytecode makeInitMethodCall(CtBehavior behavior, String method, int nbParameters, String subject, String... names) {
        Bytecode b = new Bytecode(behavior.getMethodInfo().getConstPool());
        b.addLdc(method);
        b.addIconst(nbParameters);
        if(subject == null)
            b.add(b.ACONST_NULL);
        else b.addLdc(subject);
        b.addIconst(names.length);
        b.addAnewarray("java.lang.String");
        for(int i = 0; i < names.length; i++) {
            if(names[i] != null)
                b.add(b.DUP);
        }
        for(int i = 0; i < names.length; i++) {
            if(names[i] != null) {
                b.addIconst(i);
                b.addLdc(names[i]);
                b.add(b.AASTORE);
            }
        }
        b.addInvokestatic("play.classloading.enhancers.LVEnhancer$LVEnhancerRuntime", "initMethodCall", "(Ljava/lang/String;ILjava/lang/String;[Ljava/lang/String;)V");
        //System.out.println("makeInitMethodCall => " + b.length());
        return b;
    }
    
    private static Bytecode makeExitMethod(CtBehavior behavior, String className, String methodName, String signature) {
        Bytecode b = new Bytecode(behavior.getMethodInfo().getConstPool());
        b.addLdc(className);
        b.addLdc(methodName);
        b.addLdc(signature);
        b.addInvokestatic("play.classloading.enhancers.LVEnhancer$LVEnhancerRuntime", "exitMethod", "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V");
        return b;
    }
    
    private static Bytecode makeEnterMethod(CtBehavior behavior, String className, String methodName, String signature) {
        Bytecode b = new Bytecode(behavior.getMethodInfo().getConstPool());
        b.addLdc(className);
        b.addLdc(methodName);
        b.addLdc(signature);
        b.addInvokestatic("play.classloading.enhancers.LVEnhancer$LVEnhancerRuntime", "enterMethod", "(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V");
        return b;
    }
    
    private static void insert(Bytecode b, CtClass ctClass, CtBehavior behavior, CodeAttribute codeAttribute, FrameIterator iterator, Frame frame, boolean after) throws CompileError, BadBytecode, NotFoundException {
        int locals = b.getMaxLocals();
        int maxLocals = codeAttribute.getMaxLocals();
        codeAttribute.setMaxLocals(locals > maxLocals ? locals : maxLocals);
        File debugDir = new File(Play.applicationPath, "lvenhancer-debug-" + startedAt);
        if(!debugDir.exists())
            debugDir.mkdir();
        debugDir = new File(debugDir, ctClass.getName() + "." + behavior.getName() + "-" + Codec.UUID());
        debugDir.mkdir();
        ctClass.debugWriteFile(debugDir.getAbsolutePath());
        try {
            iterator.insert(b.get(), after);
        } catch (BadBytecode bb) {
            Logger.error(bb, "(check in lvenhancer-debug-%s) error while applying LVEnhancer on %s", startedAt, behavior.getLongName());
            Logger.error("with statement: \n\tUnknown\n\nproduced:\n\t%s", Codec.byteToHexString(b.get()));
            throw bb;
        }
        try {
            codeAttribute.setMaxStack(codeAttribute.computeMaxStack());
        } catch (BadBytecode bb) {
            Logger.error(bb, "(check in lvenhancer-debug-%s) [computeMaxStack] error while applying LVEnhancer on %s", startedAt, behavior.getLongName());
            Logger.error("with statement: \n\tUnknown\n\nproduced:\n\t%s", Codec.byteToHexString(b.get()));
            throw bb;
        }
        debugDir.delete();
    }

    private static void insert(String stmt, CtClass ctClass, CtBehavior behavior, CodeAttribute codeAttribute, FrameIterator iterator, Frame frame, boolean after) throws CompileError, BadBytecode, NotFoundException {
        Javac jv = new Javac(ctClass);
        jv.recordLocalVariables(codeAttribute, frame.index);
        jv.recordParams(behavior.getParameterTypes(), Modifier.isStatic(behavior.getModifiers()));
        jv.setMaxLocals(codeAttribute.getMaxLocals());
        jv.compileStmnt(stmt);

        Bytecode b = jv.getBytecode();
        insert(b, ctClass, behavior, codeAttribute, iterator, frame, after);
    }

    private static Integer computeMethodHash(CtClass[] parameters) {
        String[] names = new String[parameters.length];
        for (int i = 0; i < parameters.length; i++) {
            names[i] = parameters[i].getName();
        }
        return computeMethodHash(names);
    }

    public static Integer computeMethodHash(Class<?>[] parameters) {
        String[] names = new String[parameters.length];
        for (int i = 0; i < parameters.length; i++) {
            Class<?> param = parameters[i];
            names[i] = "";
            if (param.isArray()) {
                int level = 1;
                param = param.getComponentType();
                // Array of array
                while (param.isArray()) {
                    level++;
                    param = param.getComponentType();
                }
                names[i] = param.getName();
                for (int j = 0; j < level; j++) {
                    names[i] += "[]";
                }
            } else {
                names[i] = param.getName();
            }
        }
        return computeMethodHash(names);
    }

    public static Integer computeMethodHash(String[] parameters) {
        StringBuffer buffer = new StringBuffer();
        for (String param : parameters) {
            buffer.append(param);
        }
        Integer hash = buffer.toString().hashCode();
        if (hash < 0) {
            return -hash;
        }
        return hash;
    }

    public static class LVEnhancerRuntime {
        private static ThreadLocal<Stack<MethodExecution>> methodParams = new ThreadLocal<Stack<MethodExecution>>();

        public static void enterMethod(String clazz, String method, String signature) {
            getCurrentMethodParams().push(new MethodExecution());
        }

        public static void exitMethod(String clazz, String method, String signature) {
            getCurrentMethodParams().pop();
        }

        public static void initMethodCall(String method, int nbParams, String subject, String[] paramNames) {
            /*if(!("<init>".equals(method) || "equals".equals(method) || "compareTo".equals(method)))
                System.out.println("init method call " + method + Arrays.toString(paramNames));*/
            getCurrentMethodParams().peek().currentNestedMethodCall = new MethodExecution(subject, paramNames, nbParams);
            Logger.trace("initMethodCall for '" + method + "' with " + Arrays.toString(paramNames));
        }
        
        /**
         * Replace the current methodParams stack by the given one.
         * Don't use it unless you know exactly what you do.
         * @param init the stack to restore.
         */
        public static void reinitRuntime(Stack<MethodExecution> init) {
            methodParams.set(init);
        }
        
        /**
         * Get the current stack of methodExecutions.
         * This should not be altered unless you know exactly what you do.
         * @return the current stack of methodExecutions.
         */
        public static Stack<MethodExecution> getCurrentMethodParams() {
            Stack<MethodExecution> result = methodParams.get();
            if(result == null) {
                result = new Stack<MethodExecution>();
                methodParams.set(result);
            }
            return result;
        }

        public static ParamsNames getParamNames() {
            Stack<MethodExecution> stack = getCurrentMethodParams();
            if(stack.size() > 0) {
                MethodExecution me = getCurrentMethodExecution();
                return new ParamsNames(me.subject, me.paramsNames, me.varargsNames);
            }
            throw new UnexpectedException("empty methodParams!");
        }

        protected static LVEnhancer.MethodExecution getCurrentMethodExecution() {
            Stack<MethodExecution> stack = getCurrentMethodParams();
            if(stack.size() > 0)
                return stack.get(stack.size() - 1).currentNestedMethodCall;
            throw new UnexpectedException("empty methodParams!");
        }

        public static class ParamsNames {
            public final String subject;
            public final String[] params;
            public final String[] varargs;

            public boolean hasVarargs() {
                return varargs != null;
            }

            public String[] mergeParamsAndVarargs() {
                Logger.trace("ParamsNames: %s :: %s", Arrays.toString(params), Arrays.toString(varargs));
                if(!hasVarargs())
                    return Arrays.copyOf(params, params.length);
                String[] result = new String[params.length + varargs.length - 1];
                for(int i = 0; i < params.length - 1; i++)
                    result[i] = params[i];
                for(int i = 0, j = params.length - 1; i < varargs.length; i++, j++)
                    result[j] = varargs[i];
                return result;
            }

            public ParamsNames(String subject, String[] params, String[] varargs) {
                this.subject = subject;
                this.params = params;
                this.varargs = varargs;
            }
            
            @Override
            public String toString() {
                return "Params: subject=" + subject + ", params=" + Arrays.toString(params) + ", varargs=" + Arrays.toString(varargs);
            }
        }
    }

    public static class MethodExecution {
        protected String[] paramsNames;
        protected String[] varargsNames;
        protected String subject;
        protected MethodExecution currentNestedMethodCall;

        private MethodExecution() { }

        private MethodExecution(String subject, String[] params, int nb) {
            this.subject = subject;
            paramsNames = Arrays.copyOfRange(params, 0, nb);
            if(nb < params.length)
                varargsNames = Arrays.copyOfRange(params, nb, params.length);
            else varargsNames = null;
        }

        public String[] getParamsNames() {
            return paramsNames;
        }

        public String[] getVarargsNames() {
            return varargsNames;
        }

        public String getSubject() {
            return subject;
        }

        public MethodExecution getCurrentNestedMethodCall() {
            return currentNestedMethodCall;
        }
    }
}