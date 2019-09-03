/**
 * MIT License

Copyright (c) 2019 Mehmet Aziz Yirik

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
 */


package EQGen;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.text.DecimalFormat;

import org.apache.commons.cli.*;
import org.openscience.cdk.depict.DepictionGenerator;
import org.openscience.cdk.exception.CDKException;
import org.openscience.cdk.graph.ConnectivityChecker;
import org.openscience.cdk.interfaces.IAtom;
import org.openscience.cdk.interfaces.IAtomContainer;
import org.openscience.cdk.interfaces.IBond;
import org.openscience.cdk.interfaces.IBond.Order;
import org.openscience.cdk.io.SDFWriter;
import org.openscience.cdk.silent.Atom;
import org.openscience.cdk.tools.SaturationChecker;
import org.openscience.cdk.tools.manipulator.BondManipulator;

import com.google.common.collect.ListMultimap;
import com.google.common.collect.MultimapBuilder;



public class Generator {
	public static SaturationChecker saturation;
	public static ConnectivityChecker conCheck;
	public static boolean verbose = false;
	static String filedir = null;
	static String molinfo= null;
	public static Map<String, Integer> valences; 
	static {
		//The atom valences from CDK.
		valences = new HashMap<String, Integer>();
			
		valences.put("C", 4);
		valences.put("N", 5);
		valences.put("O", 2);
		valences.put("S", 6);
		valences.put("P", 5);
		valences.put("F", 1);
		valences.put("I", 7);
		valences.put("Cl", 5);
		valences.put("Br", 5);
		valences.put("H", 1);
	}
	
	//This function takes a string of atom-implicit hydrogen information to build an atomcontainer
	public static IAtomContainer build(String mol) {
		IAtomContainer atomcontainer = new org.openscience.cdk.silent.AtomContainer();
		List<String> symbols = new ArrayList<String>();
	    List<Integer> hydrogens = new ArrayList<Integer>();
	    String[] atoms = mol.split("(?=[A-Z])");
	    for (String atom : atoms) {
	    	String[] info = atom.split("(?=[0-9])", 2);   
	        symbols.add(info[0]);
	        hydrogens.add(info.length > 1 ? Integer.parseInt(info[1]):0);
	    }
	        
	    for(int i=0;i<symbols.size();i++) {
	        atomcontainer.addAtom(new Atom(symbols.get(i)));
	        atomcontainer.getAtom(i).setImplicitHydrogenCount(hydrogens.get(i));
	    }
	    return atomcontainer;
	}
	
	//Saturation checker, checking the maximum number of connected bonds of atoms.
	public static boolean satcheck(IAtomContainer mol, int i) throws CloneNotSupportedException, CDKException, IOException{
		if ((mol.getAtom(i).getImplicitHydrogenCount()+ordsum(mol,i))>= (int)valences.get(mol.getAtom(i).getSymbol())){ 
			return false;
		}else{
			return true;
		}
	}
	
	//Summation of the connected bond orders.
	public static int ordsum(IAtomContainer mol, int i){
		int count=0;
		for(IBond bond: mol.getConnectedBondsList(mol.getAtom(i))){
			count=count+bond.getOrder().numeric();
		}
		return count;
	}
		
	public static final Comparator<String> ASC_ORDER = new Comparator<String>() {
	    public int compare(String e1, String e2) { 
	        return -e2.compareTo(e1);
	    }
	};
	
	//The equivalent classes of molecules are ordered and enumerated in ascending order based on their open values and implicit hydrogens; as described in the paper. 
	public static ListMultimap<String,Integer> ecenumlist(IAtomContainer acontainer) throws CloneNotSupportedException, CDKException, IOException {
		ListMultimap<String,Integer> classes = MultimapBuilder.treeKeys(ASC_ORDER).arrayListValues().build();
		//long[] sym=canonsym(acontainer);
		for(int i=0; i<acontainer.getAtomCount();i++){
			//if(satcheck(acontainer, i)==true){	
				//classes.put(acontainer.getAtom(i).getSymbol()+opencounter(acontainer, i)+Long.valueOf(sym[i]).intValue(), i); //The open sites and the sym values are used for labelling. Less interactions for an atom means lower sym values.
				classes.put(acontainer.getAtom(i).getSymbol()+(valences.get(acontainer.getAtom(i).getSymbol())-acontainer.getAtom(i).getImplicitHydrogenCount()), i);
			//}
		}		
		return classes;
	}
	
	// Molecule depiction Generator
	public static void depict(IAtomContainer mol, String path) throws CloneNotSupportedException, CDKException, IOException{
		DepictionGenerator depict = new DepictionGenerator();
		depict.withCarbonSymbols().withSize(1000, 1000).withZoom(4).depict(mol).writeTo(path);
	}
	
	/**
	 * This function extends the molecule until the chosen index, atom, is saturated.
	 */
	public static List<IAtomContainer> atomSat(IAtomContainer mol,int index, List<IAtomContainer> satList) throws CloneNotSupportedException, CDKException, IOException {
		List<IAtomContainer> mols= new ArrayList<IAtomContainer>();
		ListMultimap<String, Integer> ec= ecenumlist(mol);
		List<Integer> indices= ec.get(findClass(ec, index));
		mols=atomExt(mol,ec,indices,index,mols);
        for(IAtomContainer ac:mols) {
        	if(satcheck(ac,index)) {
        		satList=atomSat(ac,index,satList);
        	}else if(!satcheck(ac,index)) {
        		satList.add(ac);
        	}
        }
        return satList;
	}
	
	public static boolean allSaturated(List<IAtom> list, IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		boolean check=true;
		for(IAtom atom:list) {
			if(!saturation.isSaturated(atom, mol)) {
				check=false;
				break;
			}
		}
		return check;
	}
	
	public static boolean subSaturation(IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		boolean check=false;
		if(!saturation.isSaturated(mol)) {
			for(IAtom atom:mol.atoms()) {
				List<IAtom> v= new ArrayList<IAtom>();
				v.add(atom);
				check=subSaturation(mol,atom,v);
				if(check) {
					break;
				}
			}
		}
		return check;
	}
	
	public static boolean subSaturation(IAtomContainer mol, IAtom atom, List<IAtom> v) throws CDKException {
		boolean check=true;
		saturation= new SaturationChecker();
		if(saturation.isSaturated(mol)) {
			check=true;
		}else {
			if(saturation.isSaturated(atom, mol)) {
				List<IAtom> nei= mol.getConnectedAtomsList(atom);
				nei.removeAll(v);
				if(allSaturated(nei,mol)) {
					for(IAtom atom2:nei) {
						v.add(atom2);
						subSaturation(mol,atom2,v);
					}
				}else {
					check=false;
				}
			}
			else {
				check=false;
			}
		}
		return check;
	}
	
	public static List<IAtomContainer> classSat(IAtomContainer mol, List<Integer> indices, List<IAtomContainer> satList) throws CloneNotSupportedException, CDKException, IOException{
		if(indices.size()==0) {
			satList.add(mol);
		}else {
			int ind= (Integer)indices.get(0);
			List<Integer> cls2= new ArrayList<Integer>();
			for(Integer j:indices) {
				cls2.add(j);
			}
			cls2.remove((Integer)ind);
			List<IAtomContainer> atomSatList = new ArrayList<IAtomContainer>();
			atomSatList=atomSat(mol,ind, atomSatList);
			for(IAtomContainer ac: atomSatList) {
				//if(!subSaturation(ac)) { 
					satList=classSat(ac,cls2,satList);
				//}
			}
			/**for(Integer index: indices) { //Her ne kadar cl2 yaratsam da bu diğer indexler icin
				//yine atomsat yapyor ne farketti. 
				List<Integer> cls2= new ArrayList<Integer>();
				for(Integer j:indices) {
					cls2.add(j);
				}
				cls2.remove(index);
				List<IAtomContainer> atomSatList = new ArrayList<IAtomContainer>();
				atomSatList=atomSat(mol,index,outFile, atomSatList);
				for(IAtomContainer ac: atomSatList) {
					//if(!subSaturation(ac)) {
						satList=classSat(ac,cls2,satList,outFile);
					//}
				}
			}**/
		}
		return satList;
	}
	
	public static boolean CNI(ListMultimap<String, Integer> ec, List<Integer> eClass, IAtomContainer mol) {
		boolean check=true;
		for(Integer i:eClass) {
			for(String k:ec.keys()) {
				List<Integer> list= ec.get(k);
				for(Integer j: list) {
					if(i!=j) {
						if(mol.getBond(mol.getAtom(i), mol.getAtom(j))!=null) {
							check=false;
							break;
						}
					}
				}
			}
		}
		return check;
	}
	
	public static List<IAtomContainer> run( IAtomContainer mol, SDFWriter outFile, List<IAtomContainer> list) throws CloneNotSupportedException, CDKException, IOException {
		saturation = new SaturationChecker();
		if(saturation.allSaturated(mol)) {
			list.add(mol);
			outFile.write(mol);
		}else {
			ListMultimap<String, Integer> m=ecenumlist(mol);
			for(String k:m.keySet()) {
				List<Integer> l= m.get(k);
				List<IAtomContainer> kel= new ArrayList<IAtomContainer>();
				kel=classSat(mol,l,kel);
				for(IAtomContainer a: kel) {
					if(!subSaturation(a)) {
						list=run(a,outFile,list);
					}
				}
			}
		}
		return list;
	}
	
	/**
	 * This functions detects the target atom to add a bond between the chosen index and
	 * the others.
	 */
	public static int targetatom(ListMultimap<String, Integer> ec, String key, int index) {
		int target=0;
		List<Integer> indices=ec.get(key);
		if(indices.contains(index) && indices.size()>1) { //If size is 1 no need to consider
			if(indices.indexOf(index)!=indices.size()-1) {
				target+= indices.get(indices.indexOf(index)+1);
			}else if(indices.indexOf(index)==indices.size()-1) {
				target+= indices.get(indices.indexOf(index)-1);
			}
		}else {
			target+= indices.get(0);
		}
		return target;
	}
	
	/**
	 * The function add a bond between two atoms or increase the order of the bond.
	 */
	public static void bondadder(IAtomContainer mol, int index, int target)throws CloneNotSupportedException, CDKException, IOException {
		IBond add = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		if(add == null){ 					
			mol.addBond(index, target, IBond.Order.SINGLE);
		}
		else{
			BondManipulator.increaseBondOrder(add); 
		}
	}
	
	public static IAtomContainer molClone(IAtomContainer mol) {
		IAtomContainer mol2 = new org.openscience.cdk.silent.AtomContainer();
		for(IAtom atom: mol.atoms()) {
			mol2.addAtom(atom);
		}
		for(IBond bond: mol.bonds()) {
			mol2.addBond(bond);
		}
		return mol2;
	}
	
	public static String findClass(ListMultimap<String,Integer> classes, int index) {
		String output="";
		for(String key:classes.keys()) {
			if(classes.get(key).contains(index)) {
				output+=key;
				break;
			}
		}
		return output;
	}
	
	public static String lastClass(int index, IAtomContainer mol,ListMultimap<String, Integer> ec) {
		List<IAtom> cons= mol.getConnectedAtomsList(mol.getAtom(index)); 
		String out="";
		if(cons.size()==0) {
			out+=findClass(ec,index);
		}else {
			IAtom lastAtom= cons.get(cons.size()-1);
			out+=findClass(ec,mol.indexOf(lastAtom));
		}
		return out;
	}
	
	public static int lastInt(int index,IAtomContainer mol) {
		List<IAtom> cons= mol.getConnectedAtomsList(mol.getAtom(index));
		int out=0;
		if(cons.size()!=0) {
			IAtom lastAtom= cons.get(cons.size()-1);
			out+=mol.getConnectedAtomsList(lastAtom).size();
		}
		return out;
	}
	
	public static boolean lastIntCheck(int index,List<Integer> targetClass, IAtomContainer mol) {
		boolean check=true;
		int last= lastInt(index,mol);
		for(Integer i:targetClass) {
			int count= mol.getConnectedAtomsList(mol.getAtom(i)).size();
			if(count<last) {
				check=false;
				break;
			}
		}
		return check;
	}
	
	public static  List<IAtomContainer> atomextOne(IAtomContainer mol,ListMultimap<String, Integer> ec, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 	
		for(String key:ec.keySet()) {
			//System.out.println(key+" "+lastClass(index,mol,ec)+" "+ec+" "+index+" "+say+" "+count);
			//if(key.compareTo(lastClass(index,mol,ec))>=0) {
				//System.out.println("buyuk"+" "+key+" "+lastClass(index,mol,ec)+" "+say+" "+count);
				//List<Integer> l=ec.get(key);
				//if(lastIntCheck(index,l,mol)) {
					//if(CNI(index,l,mol)) {
				//int target=l.get(0); sifir olmaz kendi classindan dolayi.
				int target=targetatom(ec,key,index);
				if(index!=target && satcheck(mol,index) && satcheck(mol,target)){ 
					bondadder(mol,index,target);
					IAtomContainer mol2=mol.clone();
					mols.add(mol2);
					removeBond(mol,index,target);
				}
			//}
		}
		return mols;
	}
	
	public static List<IAtomContainer> atomextAll(IAtomContainer mol, ListMultimap<String, Integer> ec, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 	
		for(String key:ec.keySet()) {
			//System.out.println(key+" "+lastClass(index,mol,ec)+" "+ec+" "+" "+say+" "+count);
			//if(key.compareTo(lastClass(index,mol,ec))>=0) {
				//System.out.println("buyuk"+" "+key+" "+lastClass(index,mol,ec)+" "+say+" "+count);
				List<Integer> l=ec.get(key);
				for(Integer i:l) {
					if(index!=i && satcheck(mol,index) && satcheck(mol,i)){ 
						bondadder(mol,index,i);
						IAtomContainer mol2=mol.clone();
						mols.add(mol2);
						removeBond(mol,index,i);
					}
				}
			//}
		}	
		return mols;
	}
	
	public static List<IAtomContainer> atomExt(IAtomContainer mol, ListMultimap<String, Integer> ec,List<Integer> indices, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 		
		if(CNI(ec,indices,mol)) {
			mols=atomextOne(mol,ec,index,mols);
		}else {
			mols=atomextAll(mol,ec,index,mols);
		}
		
		return mols;
	}
	
	public static void removeBond(IAtomContainer mol, int index, int target) {
		IBond bond = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		if(bond.getOrder()==Order.SINGLE) {
			mol.removeBond(bond);
		}else {
			BondManipulator.decreaseBondOrder(bond);
		}
	}
	
	/**
	 * Function is for the initialisation of the inputs and recording the duration time.
	 */
	public static void HMD(String molinfo, String filedir) throws CloneNotSupportedException, CDKException, IOException {
		long startTime = System.nanoTime(); //Recording the duration time.
		SDFWriter outFile = new SDFWriter(new FileWriter(filedir+"output.sdf"));
		List<IAtomContainer> mols= new ArrayList<IAtomContainer>();
		IAtomContainer mol=build(molinfo);
		if(verbose) {
			System.out.println("Input molecule is built and its image is stored in the given directory.");
			//depict(mol,filedir+"inputmolecule.png");
		}
        //mols.add(mol);
        if(verbose) System.out.println("Start generating structures ...");
        run(mol,outFile,mols);
        //genall(mols,ecindices(mol),outFile);
        long endTime = System.nanoTime()- startTime;
        double seconds = (double) endTime / 1000000000.0;
		DecimalFormat d = new DecimalFormat(".###");
        if(verbose) {
        	//System.out.println("Number of generated structures:"+" "+uniquecheck.size());
        	System.out.println("Duration:"+" "+d.format(seconds)); //Format is second
        }
        outFile.close();	
	}
	
	private void parseArgs(String[] args) throws ParseException
	{
		Options options = setupOptions(args);	
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(options, args);
			Generator.molinfo = cmd.getOptionValue("molecularinfo");
			Generator.filedir = cmd.getOptionValue("filedir");
			
			if (cmd.hasOption("verbose")) Generator.verbose = true;
		
		} catch (ParseException e) {
			// TODO Auto-generated catch block
			HelpFormatter formatter = new HelpFormatter();
			formatter.setOptionComparator(null);
			String header = "\nGenerates structures for a given molecular information."
					+ " The input is the string of atom symbols with their number of implicit hydrogen."
					+ "For example 'C3C3C3' means three carbon atoms each of which has three implicit hydrogens."
					+ "Besides this molecular information, the directory is needed to be specified for the output"
					+ "file. \n\n";
			String footer = "\nPlease report issues at https://github.com/MehmetAzizYirik/HMD";
			formatter.printHelp( "java -jar HMD.jar", header, options, footer, true );
			throw new ParseException("Problem parsing command line");
		}
	}
	
	private Options setupOptions(String[] args)
	{
		Options options = new Options();
		Option molinfo = Option.builder("i")
			     .required(true)
			     .hasArg()
			     .longOpt("molecularinfo")
			     .desc("String of atoms with their implicit hydrogen information (required)")
			     .build();
		options.addOption(molinfo);
		Option verbose = Option.builder("v")
			     .required(false)
			     .longOpt("verbose")
			     .desc("Print messages about the duration time of the Gen")
			     .build();
		options.addOption(verbose);	
		Option filedir = Option.builder("d")
			     .required(true)
			     .hasArg()
			     .longOpt("filedir")
			     .desc("Creates and store the output sdf file in the directory (required)")
			     .build();
		options.addOption(filedir);
		return options;
	}
	
	public static void main(String[] args) throws CloneNotSupportedException, CDKException, IOException  {		
		// TODO Auto-generated method stub
		
		/**IAtomContainer ac= build("C3C3C3C2C1");
		ac.addBond(0, 3, Order.SINGLE);
		ac.addBond(3, 4, Order.SINGLE);
		ac.addBond(4, 1, Order.SINGLE);
		//ac.addBond(4, 2, Order.SINGLE);
		
		//List<IAtom> list= ac.getConnectedAtomsList(ac.getAtom(4));
		ListMultimap<String, Integer> ec=ecenumlist(ac);
		System.out.println(ec);
		System.out.println(lastClass(4,ac,ec));**/
		Generator gen = null;
		String[] args1= {"-i","C3C3C2C2C1C1","-v","-d","C:\\Users\\mehme\\Desktop\\"};
		try {
			gen = new Generator();
			gen.parseArgs(args1);
			Generator.HMD(Generator.molinfo, Generator.filedir);
		} catch (Exception e) {
			// We don't do anything here. Apache CLI will print a usage text.
			if (Generator.verbose) e.getCause(); 
		}

	}
}
