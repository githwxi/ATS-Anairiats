class Hello {
	public native void printHello();  //native method
	public native void printHelloFrom(String whom);  //native method
        public static native String hello(); // native method
	static   //static initializer code
	{
	    String ATSHOME = System.getenv("ATSHOME") ;
	    System.load(ATSHOME + "/contrib/JNI/TEST/libats_Hello.so") ;
	}
 
	public static void main(String[] args)
	{
		Hello hw = new Hello();
		hw.printHello();
		hw.printHelloFrom("ATS");
		System.out.print(hello());
	}
}
