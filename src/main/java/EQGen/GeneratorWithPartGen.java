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

import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;
import java.text.DecimalFormat;

import org.apache.commons.cli.*;
import org.openscience.cdk.exception.CDKException;
import org.openscience.cdk.graph.ConnectivityChecker;
import org.openscience.cdk.graph.GraphUtil;
import org.openscience.cdk.graph.invariant.Canon;
import org.openscience.cdk.graph.invariant.EquivalentClassPartitioner;
import org.openscience.cdk.group.AtomContainerDiscretePartitionRefiner;
import org.openscience.cdk.group.PartitionRefinement;
import org.openscience.cdk.group.PartitionRefinement.BondRefinerBuilder;
import org.openscience.cdk.group.Permutation;
import org.openscience.cdk.group.PermutationGroup;
import org.openscience.cdk.interfaces.IAtom;
import org.openscience.cdk.interfaces.IAtomContainer;
import org.openscience.cdk.interfaces.IBond;
import org.openscience.cdk.interfaces.IChemObjectBuilder;
import org.openscience.cdk.interfaces.IIsotope;
import org.openscience.cdk.interfaces.IBond.Order;
import org.openscience.cdk.interfaces.IMolecularFormula;
import org.openscience.cdk.io.SDFWriter;
import org.openscience.cdk.io.iterator.IteratingSDFReader;
import org.openscience.cdk.signature.MoleculeSignature;
import org.openscience.cdk.signature.Orbit;
import org.openscience.cdk.silent.Atom;
import org.openscience.cdk.silent.AtomContainer;
import org.openscience.cdk.depict.DepictionGenerator;
import org.openscience.cdk.silent.SilentChemObjectBuilder;
import org.openscience.cdk.tools.SaturationChecker;
import org.openscience.cdk.tools.manipulator.AtomContainerManipulator;
import org.openscience.cdk.tools.manipulator.BondManipulator;
import org.openscience.cdk.tools.manipulator.MolecularFormulaManipulator;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.MultimapBuilder;



public class GeneratorWithPartGen {
	public static IChemObjectBuilder builder =SilentChemObjectBuilder.getInstance();
	public static Set<String> signatureCheck = new HashSet<String>();
	public static SaturationChecker saturation;
	public static ConnectivityChecker conCheck;
	public static boolean verbose = false;
	public static String fragments = null;
	public static String filedir = null;
	public static String molinfo= null;
	public static int totalOpenSites=0;
	public static int[] valence1Count;
	public static String[]  valence1Symbol;
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
		valences.put("I", 1);
		valences.put("Cl", 1);
		valences.put("Br", 1);
		valences.put("H", 1);
	}
	
	/**
	 * Comparators.
	 */
	
	public static final Comparator<String> ASC_ORDERS = new Comparator<String>() {
	    public int compare(String e1, String e2) { 
	        return -e2.compareTo(e1);
	    }
	};
	
	public static final Comparator<Integer> ASC_ORDERI = new Comparator<Integer>() {
	    public int compare(Integer e1, Integer e2) { 
	        return -e2.compareTo(e1);
	    }
	};
	
	/**
	 * General Functions
	 */
	
	/**
	 * Checks an int array is in the list or not.
	 * @param list ArrayList of int arrays
	 * @param arr int array
	 * @return boolean true if the array is in the list
	 */
	
	public static boolean inTheList(ArrayList<int[]> list, int[] arr) {
		boolean check= false;
		for(int i=0;i<list.size();i++) {
			if(Arrays.equals(list.get(i), arr)) {
				check=true;
				break;
			}
		}
		return check;
	 }
	 
	/**
	 * Sum all array entries.
	 * @param array int array
	 * @return
	 */
	
	public static int sum(int[] array) {
		int sum=0;
		for(int i=0;i<array.length;i++) {
			sum=sum+array[i];
		}
		return sum;
	}
	
	/**
	 * Sum array entries until the given index
	 * @param array int array
	 * @return
	 */
	
	public static int sum(int[] array, int index) {
		int sum=0;
		for(int i=0;i<=index;i++) {
			sum=sum+array[i];
		}
		return sum;
	}
	/**
	 * Checks whether the list is in the list of the lists or not.
	 * @param list List of ArrayList<Integer>
	 * @param arr list of integers
	 * @return true if the list is in the list of lists.
	 */
	
	public static boolean inTheList(HashSet<ArrayList<Integer>> list, ArrayList<Integer> arr) {
		 boolean check= false;
		 for(ArrayList<Integer> l:list) {
			 if(l.equals(arr)) {
				 check=true;
				 break;
			 }
		 }
		 return check;
	 }
	
	/**
	 * Removing an index from a list, then updating it.
	 * @param list integer list
	 * @param index index to remove.
	 * @return List<Integer> new integer list
	 */
	
	public static List<Integer> updateList(List<Integer> list, int index){
		List<Integer> listNew= new ArrayList<Integer>();
		for(Integer j:list) {
			listNew.add(j);
		}
		listNew.remove((Integer)index);
		return listNew;
	}
	
	/**
	 * Permutation Group Functions - Fundamental Lemma of Orbits
	 * More details: Mathematical Chemistry and Cheminformatics book.
	 */
	
	/**
	  * Generating list of unique orbits for the list of truncated tabloids
	  * and the acting group.The method is given in MOLGEN Book Page 80. 
	  * The method is explained also with an example (Example 3.31) Page 167.
	  * 
	  * 
	  * @param truncated truncated tabloids for the acting group
	  * @param group a permutation group 
	  * @return list of unique orbits
	  */
	 
	 public static Set<Set<ArrayList<Integer>>> fundamentalLemma(PermutationGroup group, PermutationGroup group2, int trun, ArrayList<Permutation> group3) {
		 Set<Set<ArrayList<Integer>>> orbits= new HashSet<Set<ArrayList<Integer>>>(); 
		 List<int[]> list= new ArrayList<int[]>();
		 int[] array= new int[0];
		 List<int[]> truncated= truncatedTabloidsInitial(trun,array,list);
		 for(int j=0;j<truncated.size();j++) {
			Set<ArrayList<Integer>> orbit= new HashSet<ArrayList<Integer>>();
		    for(Permutation perm: group3) {
		    	ArrayList<Integer> l= new ArrayList<Integer>();
		    	for(int k=0;k<truncated.get(j).length;k++) {
		    		l.add(perm.get(truncated.get(j)[k]));
		    	}
		    	l.sort(ASC_ORDERI);
		    	orbit.add(l);
		    }
		    orbits.add(orbit);
		  }
		 
		 return orbits;
	 }
	  
	 public static int count=0;
	 public static Set<String> check= new HashSet<String>();
	 public static Set<Set<ArrayList<Integer>>> fundamentalLemma(IAtomContainer ac) throws CloneNotSupportedException, CDKException, IOException {
		 Set<Set<ArrayList<Integer>>> orbits= new HashSet<Set<ArrayList<Integer>>>();
		 int startIndex= ac.getAtomCount();
		 List<int[]> truncated= truncatedTabloids(valence1Count,startIndex);
		 openSiteAdder(ac);
		 PermutationGroup group= getAutomorphismGroup(ac);
		 for(int j=0;j<truncated.size();j++) {
			Set<ArrayList<Integer>> orbit= new HashSet<ArrayList<Integer>>();
		    for(Permutation perm: group.all()) {
		    	ArrayList<Integer> l= new ArrayList<Integer>();
		    	for(int k=0;k<truncated.get(j).length;k++) {
		    		l.add(perm.get(truncated.get(j)[k]));
		    	}
		    	//l.sort(ASC_ORDERI);
		    	orbit.add(l);
		    }
		    orbits.add(orbit);
		    count++;
		    IAtomContainer newAc= distributeValence1Atoms(ac,getRepresentative(orbit),valence1Symbol);
		    if(signatureCheck.add(moleculeSignature(newAc))) {
		    	depict(newAc,"C:\\Users\\mehme\\Desktop\\output\\"+count+".png");
		    }
		  }
		 
		 return orbits;
	 }
	 
	 public static ArrayList<Integer> getRepresentative(Set<ArrayList<Integer>> orbits){
		 ArrayList<Integer> orbit= new ArrayList<Integer>();
		 for(ArrayList<Integer> rep:orbits) {
			 orbit=rep;
			 break;
		 }
		 return orbit;
	 }
	 
	 /**
	  * Generating a group from a list permutations
	  * @param perm a list of permutations	
	  * @return permutation group generated by a list of permutations
	  */
			
	public static PermutationGroup generateGroup(ArrayList<Permutation> list) {
		List<Permutation> generators = new ArrayList<Permutation>();
		generators.addAll(list);
		return new PermutationGroup(8, generators); // TODO: Size should be automatically given not manual
	}
	
	/**
	 * Calculating automorphism group of an atom container
	 * @param ac atom container
	 * @return PermutationGroup automorphism group 
	 */
	
	public static PermutationGroup getAutomorphismGroup(IAtomContainer ac) {
		AtomContainerDiscretePartitionRefiner refiner = PartitionRefinement.forAtoms().create();
		return refiner.getAutomorphismGroup(ac);
	}
	
	public static int[] addElement(int[] a, int e) {
		a  = Arrays.copyOf(a, a.length + 1);
	    a[a.length - 1] = e;
	    return a;
	}
	 
	 /**
	  * Truncated tabs are described in Mathematical Chemistry and Cheminformatics book. (Chapter 3)
	  * @param number
	  * @param array
	  * @param list
	  * @return list of int arrays, tabs.
	  */
	 
	 public static List<int[]> truncatedTabloidsInitial(int number, int[] array, List<int[]> list) {
		int size= array.length;
		if(size==number) {
			list.add(array);
		}else {
			if(size==0) {
				for(int i=0; i<=number;i++) {
					truncatedTabloidsInitial(number,addElement(array,i),list);
				}
			}else {
				for(int i=array[size-1]+1; i<=number+size;i++) {
					truncatedTabloidsInitial(number,addElement(array,i),list);
				}
			}
		}
		return list;
	 }
	 
	 
	 public static int[] increaseWithIndex(int[] array, int startIndex) {
		 for(int i=0;i<array.length;i++) {
			 array[i]+=startIndex;
		 }
		 return array;
	 }
	 
	 public static int[] increaseWithIndex(int[] array, int startIndex, int entryAmount) {
		 for(int i=array.length-1;i>=(array.length-entryAmount);i--) {
			 array[i]+=startIndex;
		 }
		 return array;
	 }
	 
	 public static List<int[]> truncatedTabloids(int number, int[] array, List<int[]> list, List<Integer> entries) {
		 int size= array.length;
		 if(size==number) {
			 list.add(array);
		 }else {
			for(Integer i:entries) {
				entries=updateList(entries,i);
				truncatedTabloids(number,addElement(array,i),list,entries);
			}
		 }
		 return list;
	 }
	 
	 
	 public static List<Integer> inputList(int[] array, int number){
		 List<Integer> intList= new ArrayList<Integer>();
		 for(int i=1;i<=number;i++) {
			 if(!entryCheck(array,i)) {
				 intList.add(i);
			 }
		 }
		 return intList;
	 }
	 
	 public static boolean entryCheck(int[] array, int entry) {
		 boolean check=false;
		 for(int i=0;i<array.length;i++) {
			 if(array[i]==entry) {
				 check=true;
				 break;
			 }
		 }
		 return check;
	 }
	 
	 /**
	  * or the atoms with valence 1, To count occurences of atom types in an atom container.
	  * @param mol atom container
	  * @return HashMap of atom occurunces.
	  */
	 
	 public static HashMap<String,Integer> atomsWithValence1(IAtomContainer mol){
		 HashMap<String, Integer> atomCounts = new HashMap<String, Integer>(); 
		 for(IAtom atom: mol.atoms()) {
			 String symbol = atom.getSymbol();
			 if(valences.get(symbol)==1) {
				 if(atomCounts.containsKey(symbol)) {
					 atomCounts.put(symbol, atomCounts.get(symbol)+1);
				 }else {
					 atomCounts.put(symbol, 1);
				 }
			 }
		 }
		 return sortByValue(atomCounts); 
	 }
	 
	 /**
	  * To sort a Hashmap based on the entries. 
	  * @param atomCounts HashMap<String,Integer>
	  * @return HashMap<String, Integer>
	  */
	 
	 public static HashMap<String, Integer> sortByValue(HashMap<String, Integer> atomCounts) { 
	     List<Map.Entry<String, Integer> > map2list = new LinkedList<Map.Entry<String, Integer>>(atomCounts.entrySet()); 
	     Collections.sort(map2list, new Comparator<Map.Entry<String, Integer> >() { 
	    	 public int compare(Map.Entry<String, Integer> o1, Map.Entry<String, Integer> o2){ 
	    		 return -(o1.getValue()).compareTo(o2.getValue()); 
	         } 
	     }); 
	          
	     HashMap<String, Integer> newMap = new LinkedHashMap<String, Integer>(); 
	     for (Map.Entry<String, Integer> entry : map2list) { 
	    	 newMap.put(entry.getKey(), entry.getValue()); 
	     } 
	     return newMap; 
	 } 
	 
	 public static List<int[]> truncatedTabloids(int[] entries,int startIndex){
		 List<int[]> tabloids= new ArrayList<int[]>();
		 for(int i=0;i<entries.length-1;i++) {
			 if(i==0) {
				 int[] array= new int[0];
				 tabloids = truncatedTabloidsInitial(entries[0],array,tabloids);
			 }else {
				 tabloids = truncatedTabloids(tabloids,sum(entries,i),sum(entries)-1); 
			 }
		 }
		 for(int[] array: tabloids) {
			 increaseWithIndex(array,startIndex);
		 }
		 return tabloids;
	 }
	 
	public static List<int[]> truncatedTabloids(List<int[]> tabloids,int number, int total){
		List<int[]> tabloids2= new ArrayList<int[]>();
		for(int[] tab: tabloids) {
			truncatedTabloids(number,tab,tabloids2,inputList(tab,total));
		}
		return tabloids2;
	}
	 
	/**
	 * Atom container functions
	 */
	
	/**
	 * Building an atom container from a string of atom-implicit hydrogen information.
	 * If provided, fragments are also added.
	 * @param mol molecular information
	 * @return atom container new atom container
	 * @throws IOException
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 */
	
	public static IAtomContainer build(String mol) throws IOException, CloneNotSupportedException, CDKException {
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
	    //setFlagID(atomcontainer);
	    //addFragments(atomcontainer,fragments);
	    return atomcontainer;
	}
	
	/**
	 * Setting flag for each atom in the atomcontainer for fragment construction. 
	 * @param ac atom container
	 */
	
	public static void setFlag(IAtomContainer ac) {
		for(IAtom atom: ac.atoms()) {
			atom.setFlag(1, false);
		}
	}
	
	/**
	 * Setting flag IDs for each atom in the atomcontainer for fragment construction. 
	 * @param ac atom container
	 */
	
	public static void setFlagID(IAtomContainer ac){
		for(int i=0;i<ac.getAtomCount();i++) {
			IAtom atom= ac.getAtom(i);
			atom.setFlag(1, false);
			atom.setID("no:"+i);
		}
	}
	
	/**
	 * Getting equal atoms in atom container and a fragment.
	 * @param acon atom container
	 * @param fragment fragment
	 * @return int array with the indices of the equal atoms.
	 */
	
	public static int[] getEqualAtoms(IAtomContainer acon, IAtomContainer fragment) {
		int[] equal= new int[fragment.getAtomCount()];
		for(IAtom fAtom : fragment.atoms()){
			for(IAtom atom : acon.atoms()){
				if(fAtom.getSymbol().equals(atom.getSymbol())&& fAtom.getImplicitHydrogenCount()==atom.getImplicitHydrogenCount() && (!fAtom.getFlag(1))&&(!atom.getFlag(1))){
					fAtom.setID(atom.getID());
					equal[fragment.indexOf(fAtom)]=acon.indexOf(atom);
					fAtom.setFlag(1, true);
					atom.setFlag(1, true);
					break;
				}
			}
		}
		return equal;
	}
	
	/**
	 * Adding fragments of the molecule.
	 * @param acontainer atom container
	 * @param fpath directory path for fragments file.
	 * @throws IOException
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 */
	
	public static void addFragments(IAtomContainer acontainer, String fragmentsPath) throws IOException, CloneNotSupportedException, CDKException{
		IteratingSDFReader fragments = new IteratingSDFReader(new FileReader(fragmentsPath),SilentChemObjectBuilder.getInstance());
		while (fragments.hasNext()) {
			IAtomContainer fragment=fragments.next();
			setFlag(acontainer);
			List<IAtom> done= new ArrayList<IAtom>();
			int[] equals= getEqualAtoms(acontainer,fragment);
			for(int i=0;i<equals.length;i++) {
				List<IAtom> neighbors = fragment.getConnectedAtomsList(fragment.getAtom(i));
				for(IAtom neig: neighbors){
					if(!done.contains(neig)){
						for(int j=0;j<acontainer.getAtomCount();j++){
							if(neig.getID().equals(acontainer.getAtom(j).getID())){
								done.add(fragment.getAtom(i));
								acontainer.addBond(equals[i], j,fragment.getBond(fragment.getAtom(i), neig).getOrder());
							}
						}
					}
				}
				
			}
		}
		fragments.close();
	}
	
	/**
	 * Calculating the total number of bonds connecting to the atom.
	 * @param mol atom container
	 * @param i atom index
	 * @return int summation of all bond orders for the atom.
	 */
	
	public static int getTotalBondOrder(IAtomContainer mol, int i){
		int count=0;
		for(IBond bond: mol.getConnectedBondsList(mol.getAtom(i))){
			count=count+bond.getOrder().numeric();
		}
		return count;
	}
	
	/**
	 * The equivalent classes of molecules are ordered and enumerated in ascending order 
	 * based on their open values and implicit hydrogens; as described in the paper. 
	 * @param acontainer atom container
	 * @return ListMultiMap map of atom equivalence classes
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static ListMultimap<String,Integer> equivalenceClasses(IAtomContainer acontainer) throws CloneNotSupportedException, CDKException, IOException {
		ListMultimap<String,Integer> classes = MultimapBuilder.treeKeys(ASC_ORDERS).arrayListValues().build();
		for(int i=0; i<acontainer.getAtomCount();i++){
			if(saturationChecker(acontainer, i)==true){	
				classes.put(acontainer.getAtom(i).getSymbol()+(valences.get(acontainer.getAtom(i).getSymbol())-acontainer.getAtom(i).getImplicitHydrogenCount()), i); // TODO: Valence value and the implicit info are fixed. No need to check again and again.
			}
		}		
		return classes;
	}
	
	/**
	 * Getting molecular signatures
	 * @param ac atom container
	 * @return string SIGNATURE
	 */
	
	public static String moleculeSignature(IAtomContainer ac) {
		MoleculeSignature molSig = new MoleculeSignature(ac);			
		return molSig.toCanonicalString();
	}
	
	/**
	 * Generating symmetry classes of atoms with Canon class.
	 * @param ac atom container
	 * @return long[] list of atom equivalence classes
	 */
	
	public static long[] canonSymmetry(IAtomContainer ac) {
		 int[][] g = GraphUtil.toAdjList(ac);
		 return Canon.symmetry(ac, g);
	}
	
	/**
	 * The list of equivalence classes of molecule.
	 * @param molecule atom container
	 * @return ListMultiMap<String,Integer> equivalence classes
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static ListMultimap<String,Integer> equivalenceClassList(IAtomContainer molecule) throws CloneNotSupportedException, CDKException, IOException {
		ListMultimap<String,Integer> equivalenceClasses = MultimapBuilder.treeKeys(ASC_ORDERS).arrayListValues().build();
		long[] symmetryClasses=canonSymmetry(molecule);
		for(int index=0; index<molecule.getAtomCount();index++){
			if(saturationChecker(molecule, index)==true){	
				equivalenceClasses.put(molecule.getAtom(index).getSymbol()+openSiteCounter(molecule, index)+Long.valueOf(symmetryClasses[index]).intValue(), index); //The open sites and the symmetry values are used for labelling.
			}
		}		
		return equivalenceClasses;
	}
	
	/**
	 * Count open sites of an atom in a molecule.
	 * @param mol atom container
	 * @param i atom index
	 * @return int number of open sites
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static int openSiteCounter(IAtomContainer mol, int i)throws CloneNotSupportedException, CDKException, IOException{
		//int open = valences.get(mol.getAtom(i).getSymbol()).intValue()- orderSum(mol,i) - mol.getAtom(i).getImplicitHydrogenCount(); 
		int open = valences.get(mol.getAtom(i).getSymbol()).intValue()- orderSum(mol,i) ; 
		return open;
	}
	
	/**
	 * Enumeration of open sites in a molecule.
	 * @param mol atom container
	 * @return List<Integer> List of atom indices.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<Integer> openSiteEnumerator(IAtomContainer mol) throws CloneNotSupportedException, CDKException, IOException {
		List<Integer> indices= new ArrayList<Integer>();
		for(int i=0;i<mol.getAtomCount();i++) {
			if(!saturationChecker(mol,i)) {
				for(int j=0;j<openSiteCounter(mol,i);j++) {
					indices.add(i);
				}
			}
		}
		return indices;
	}
	
	/**
	 * For the Fundamental Lemma of Orbits, the open sites are filled with atoms "R".
	 * These non-described atoms help us for the enumeration of the open sites and
	 * for the correct calculation of open sites symmetries.
	 * 
	 * @param acon IAtomContainer 
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static void openSiteAdder(IAtomContainer acon) throws CloneNotSupportedException, CDKException, IOException {
		int size=acon.getAtomCount();
		List<Integer> ind= new ArrayList<Integer>();
		for(int i=0;i<size;i++) {
			if(saturationChecker(acon,i)) {
				for(int j=0;j<openSiteCounter(acon,i);j++) {
					ind.add(i);
				}
			}
		}
		
		for(int i=0;i<ind.size();i++) {
			acon.addAtom(new Atom("R"));
			acon.addBond(ind.get(i), acon.getAtomCount()-1, Order.SINGLE);
		}
	}
	
	public static IAtomContainer distributeValence1Atoms(IAtomContainer acon, ArrayList<Integer> orbit, String[] symbols) throws CloneNotSupportedException {
		IAtomContainer ac= acon.clone();
		System.out.println(orbit);
		for(int i=0;i<orbit.size();i++) {
			System.out.println(ac.getAtom(orbit.get(i)).getSymbol()+" "+i);
			AtomContainerManipulator.replaceAtomByAtom(ac, ac.getAtom(orbit.get(i)), new Atom(symbols[i]));
		}
		for(IAtom atom: ac.atoms()) {
			if(atom.getSymbol()=="R") {
				AtomContainerManipulator.replaceAtomByAtom(ac, atom, new Atom(symbols[symbols.length-1]));
			}
		}
		return ac;
	}
	/**
	 * Counting total number of open sites in a molecule.
	 * The atoms with valence one will be distributed at the end.
	 * @param formula IMolecularFormula 
	 * @return int total number of open sites
	 */
	
	public static int totalOpenSites(IMolecularFormula formula) {
		int opens=0;
		for(IIsotope iso: formula.isotopes()) {
			int valence=valences.get(iso.getSymbol());
			for(int i=0;i<formula.getIsotopeCount(iso);i++) {
				if(valence==1) {
					opens--;
				}else {
					opens+=valences.get(iso.getSymbol());
				}
			}
		}
		return opens;
	}
	
	/**
	 * Sum all connected bond orders for an atom.
	 * @param mol atom container 
	 * @param i an atom index
	 * @return int sumation of bond orders.
	 */
	
	public static int orderSum(IAtomContainer mol, int i){
		int count=0;
		for(IBond bond: mol.getConnectedBondsList(mol.getAtom(i))){
			count=count+bond.getOrder().numeric();
		}
		return count;
	}
	
	/**
	 * Calculating the total bond order in a molecule
	 * @param mol a atom container
	 * @return int order sum
	 */
	
	public static int orderSum(IAtomContainer mol) {
		int total=0;
		for(IBond bond: mol.bonds()) {
			total+=bond.getOrder().numeric();
		}
		return total;
	}
	
	/**
	 * Molecule Depiction
	 * @param mol atom container
	 * @param path directory path for png file.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static void depict(IAtomContainer mol, String path) throws CloneNotSupportedException, CDKException, IOException{
		DepictionGenerator depict = new DepictionGenerator();
		depict.withCarbonSymbols().withSize(1000, 1000).withZoom(4).depict(mol).writeTo(path);
	}
	
	/**
	 * Saturation Checkers.
	 */
	
	/**
	 * In the atom container, checking an atom is saturated or not.
	 * @param mol atom container
	 * @param i atom index
	 * @return boolean true if atom is saturated.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static boolean saturationChecker(IAtomContainer mol, int i) throws CloneNotSupportedException, CDKException, IOException{
		//if ((mol.getAtom(i).getImplicitHydrogenCount()+getTotalBondOrder(mol,i))>= (int)valences.get(mol.getAtom(i).getSymbol())){ 
		if (orderSum(mol,i)>= (int)valences.get(mol.getAtom(i).getSymbol())){ 
			return false;
		}else{
			return true;
		}
	}
	
	/**
	 * Checking saturation of a list of atoms in a molecule.
	 * @param list list of atoms
	 * @param mol atom container
	 * @return boolean true if all atoms are saturated.
	 * @throws CDKException
	 */
	
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
	
	/**
	 * Checks whether the atom container has any saturated substructures.
	 * @param mol atom container
	 * @return boolean true if there is a saturated substructure.
	 * @throws CDKException
	 */
	
	public static boolean subSaturation(IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		boolean check=false;
		if(!saturation.isSaturated(mol)) {
			for(IAtom atom:mol.atoms()) {
				List<IAtom> atoms= new ArrayList<IAtom>();
				atoms.add(atom);
				check=subSaturation(mol,atom,atoms);
				if(check) {
					break;
				}
			}
		}
		return check;
	}
	
	/**
	 * Sub function for subSaturation function.Checking whether the neighbors of the atom are
	 * saturated or not.
	 * @param mol atom container
	 * @param atom atom 
	 * @param atoms list of atoms
	 * @return boolean true if there is a saturated substructure for the list of atoms.
	 * @throws CDKException
	 */
	
	public static boolean subSaturation(IAtomContainer mol, IAtom atom, List<IAtom> atoms) throws CDKException {
		boolean check=true;
		saturation= new SaturationChecker();
		if(saturation.isSaturated(mol)) {
			check=true;
		}else {
			if(saturation.isSaturated(atom, mol)) {
				List<IAtom> nei= mol.getConnectedAtomsList(atom);
				nei.removeAll(atoms);
				if(allSaturated(nei,mol)) {
					for(IAtom atom2:nei) {
						atoms.add(atom2);
						subSaturation(mol,atom2,atoms);
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
	
	/**
	 * Molecule Generation Functions
	 */
	
	/**
	 * 
	 * Detecting the target atom to add a bond between the chosen index and
	 * the others.
	 *
	 * @param ec equivalence classes
	 * @param key class key
	 * @param index atom index
	 * @return int target atom index
	 */
	
	public static int targetAtom(ListMultimap<String, Integer> ec, String key, int index) {
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
	 * The function add a bond between two atoms or increase the bond order.
	 * @param mol atom container
	 * @param index atom index
	 * @param target target atom index
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static void bondAdder(IAtomContainer mol, int index, int target)throws CloneNotSupportedException, CDKException, IOException {
		IBond add = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		if(add == null){ 					
			mol.addBond(index, target, IBond.Order.SINGLE);
		}
		else{
			BondManipulator.increaseBondOrder(add); 
		}
	}
	
	/**
	 * Removing a bond from an atom container
	 * @param mol atom container
	 * @param index atom index
	 * @param target target atom index
	 */
	
	public static void removeBond(IAtomContainer mol, int index, int target) {
		IBond bond = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		if(bond.getOrder()==Order.SINGLE) {
			mol.removeBond(bond);
		}else {
			BondManipulator.decreaseBondOrder(bond);
		}
	}
	
	/**
	 * Finding class of the atom index.
	 * @param classes equivalence classes
	 * @param index atom index
	 * @return String the class key of the index.
	 */
	
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
	
	/**
	 * Interacting the atom with only one atoms from each equivalence classes.
	 * @param mol atom container
	 * @param ec equivalence classes
	 * @param index atom index
	 * @param mols list of molecules
	 * @return List<IAtomContainer> list of atom containers
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static  List<IAtomContainer> atomExtensionOnce(IAtomContainer mol,ListMultimap<String, Integer> ec, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 	
		for(String key:ec.keySet()) {
			int target=targetAtom(ec,key,index);
			if(index!=target && saturationChecker(mol,index) && saturationChecker(mol,target)){ 
				bondAdder(mol,index,target);
				IAtomContainer mol2=mol.clone();
				mols.add(mol2);
				removeBond(mol,index,target);
			}
		}
		return mols;
	}
	
	/**
	 * Interacting atom with all the members of equivalence classes.
	 * @param mol atom container
	 * @param ec equivalence classes
	 * @param index atom index
	 * @param mols list of molecules
	 * @return List<IAtomContainer> list of atom containers
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<IAtomContainer> atomExtensionAll(IAtomContainer mol, ListMultimap<String, Integer> ec, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 	
		for(String key:ec.keySet()) {
			List<Integer> l=ec.get(key);
			for(Integer i:l) {
				if(index!=i && saturationChecker(mol,index) && saturationChecker(mol,i)){ 
					bondAdder(mol,index,i);
					IAtomContainer mol2=mol.clone();
					mols.add(mol2);
					removeBond(mol,index,i);
				}
			}
		}	
		return mols;
	}
	 
	 /**
	  * CNI is the isomoprhism checking method explained in the article.
	  * @param ec equivalence classes.
	  * @param eClass an equivalence class
	  * @param mol atom container
	  * @return boolean true if the CNI conditions are satisfied.
	  */
		
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
	 
	 /**
	  * Extension of atom interactions for the given atom in the atom container.
	  * @param mol atom container
	  * @param ec equivalence classes
	  * @param indices equivalence class members
	  * @param index atom index
	  * @param mols list of molecules
	  * @return List<IAtomContainer> list of atom containers
	  * @throws CloneNotSupportedException
	  * @throws CDKException
	  * @throws IOException
	  */
		
	public static List<IAtomContainer> atomExtension(IAtomContainer mol, ListMultimap<String, Integer> ec,List<Integer> indices, int index,List<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 		
		if(CNI(ec,indices,mol)) {
			mols=atomExtensionOnce(mol,ec,index,mols);
		}else {
			mols=atomExtensionAll(mol,ec,index,mols);
		}	
		return mols;
	}
	
	 /**
	  * Saturating atom in the atom container
	  * @param mol atom container
	  * @param index atom index
	  * @param satList List of molecule, in which the atom is saturated. 
	  * @return List<IAtomContainer> list of atom containers in which the atom is saturated.
	  * @throws CloneNotSupportedException
	  * @throws CDKException
	  * @throws IOException
	  */
		
	public static List<IAtomContainer> atomSaturation(IAtomContainer mol,int index, List<IAtomContainer> satList) throws CloneNotSupportedException, CDKException, IOException {
		List<IAtomContainer> mols= new ArrayList<IAtomContainer>();
		ListMultimap<String, Integer> ec= equivalenceClassList(mol);
		List<Integer> indices= ec.get(findClass(ec, index));
		mols=atomExtension(mol,ec,indices,index,mols);
	    for(IAtomContainer ac:mols) {
	    	if(saturationChecker(ac,index)) {
	    		satList=atomSaturation(ac,index,satList);
	        }else{
	        	satList.add(ac);
	        }
	     }
	     return satList;
	}
	
	 /**
	  * Saturating an equivalence class.
	  * @param mol atom container
	  * @param indices an equivalence class
	  * @param satList list of saturated molecules, for the list of indices.
	  * @return List<IAtomContainer> list of saturated molecules, for the list of indices.
	  * @throws CloneNotSupportedException
	  * @throws CDKException
	  * @throws IOException
	  */
	 
	public static List<IAtomContainer> classSat(IAtomContainer mol, List<Integer> indices, List<IAtomContainer> satList) throws CloneNotSupportedException, CDKException, IOException{
		if(indices.size()==0) {
			satList.add(mol);
		}else {
			int ind= (Integer)indices.get(0);
			List<Integer> newList= updateList(indices,ind);
			List<IAtomContainer> atomSatList = new ArrayList<IAtomContainer>();
			atomSatList=atomSaturation(mol,ind, atomSatList);
			for(IAtomContainer ac: atomSatList) {
				//if(!subSaturation(ac)) { 
					satList=classSat(ac,newList,satList);
				//}
			}
		}
		return satList;
	}
	
	 /**
	  * To start the generation process, first, by generating the equivalence classes.
	  * @param mol atom container
	  * @param outFile SDF output file
	  * @param list list of atom containers
	  * @return List<IAtomContainer> list of generated structures
	  * @throws CloneNotSupportedException
	  * @throws CDKException
	  * @throws IOException
	  */
	public static int c=0;
	public static List<IAtomContainer> generate( IAtomContainer mol, SDFWriter outFile, List<IAtomContainer> list) throws CloneNotSupportedException, CDKException, IOException {
		saturation = new SaturationChecker();
		if(totalOpenSites==orderSum(mol)*2) {
			if(signatureCheck.add(moleculeSignature(mol))) {
				list.add(mol);
				outFile.write(mol);
			}
		}else {
			ListMultimap<String, Integer> m=equivalenceClassList(mol);
			for(String k:m.keySet()) {
				List<Integer> l= m.get(k);
				List<IAtomContainer> sat= new ArrayList<IAtomContainer>();
				sat=classSat(mol,l,sat);
				for(IAtomContainer a: sat) {
					if(!subSaturation(a)) {
						if(totalOpenSites>orderSum(a)*2) {
							depict(mol,"C:\\Users\\mehme\\Desktop\\output\\"+c+".png");
							c++;
							list=generate(a,outFile,list);
						}
					}
				}
			}
		}
		return list;
	}
	
	/**
	 * The main function to set the inputs and terminate the generation functions.
	 * @param molInfo molecular information
	 * @param fileDirectory Directory path for the output SDF file.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	 
	public static void run(String molInfo, String fileDirectory) throws CloneNotSupportedException, CDKException, IOException {
		long startTime = System.nanoTime(); //Recording the duration time.
		SDFWriter outFile = new SDFWriter(new FileWriter(filedir+"output.sdf"));
		List<IAtomContainer> mols= new ArrayList<IAtomContainer>();
		IMolecularFormula formula = MolecularFormulaManipulator.getMolecularFormula(molInfo, builder);
		setVariables(formula);
		System.out.println(totalOpenSites);
		cleanValence1s(formula);
		List<int[]> rows= AdjacencyMatrixGenerator.rowsGen2(0);
		System.out.println(rows.size());
		for(int[] i: AdjacencyMatrixGenerator.rowsGen2(0)) {
			System.out.println(Arrays.toString(i));
		}
		/**List<IAtomContainer> simpleGraphs = AdjacencyMatrixGenerator.simpleAtomContainers(formula);
		int c=0;
		System.out.println(simpleGraphs.size());
		for(IAtomContainer mol: simpleGraphs) {
			depict(mol,"C:\\Users\\mehme\\Desktop\\output\\bu"+c+".png");
			c++;
        	//generate(mol,outFile,mols);
        }
		
		if(verbose) {
			System.out.println("Input molecule is built and its image is stored in the given directory.");
		}
        if(verbose) System.out.println("Start generating structures ...");
        for(IAtomContainer mol: simpleGraphs) {
        	generate(mol,outFile,mols);
        }
        long endTime = System.nanoTime()- startTime;
        double seconds = (double) endTime / 1000000000.0;
		DecimalFormat d = new DecimalFormat(".###");
        if(verbose) {
        	System.out.println("Number of generated structures:"+" "+mols.size());
        	System.out.println("Duration:"+" "+d.format(seconds)); //Format in second
        }
        outFile.close();**/	
	}
	
	public static void setVariables(IMolecularFormula formula) {
		HashMap<String, Integer> map = getValence1s(formula);
		GeneratorWithPartGen.valence1Count   = getOccurencesValence1(map);
		GeneratorWithPartGen.valence1Symbol = getSymbolsValence1(map,valence1Count);
		GeneratorWithPartGen.totalOpenSites=totalOpenSites(formula);
	}
	
	public static void cleanValence1s(IMolecularFormula formula) {
		List<IIsotope> list= new ArrayList<IIsotope>();
		
		for(IIsotope iso: formula.isotopes()) {
			String sym= iso.getSymbol();
			System.out.println(sym);
			if(valences.get(sym)==1) {
				list.add(iso);
			}
		}
		for(IIsotope iso: list) {
			formula.removeIsotope(iso);
		}
	}
	
	public static HashMap<String, Integer> getValence1s(IMolecularFormula formula){
		HashMap<String, Integer> valence1s = new HashMap<String, Integer>(); 
		for(IIsotope iso:formula.isotopes()) {
			String sym= iso.getSymbol();
			if(valences.get(sym)==1) {
				valence1s.put(sym, formula.getIsotopeCount(builder.newInstance(IIsotope.class, sym)));
			}
		}
		return sortByValue(valence1s);
	}
	
	public static int[] getOccurencesValence1(HashMap<String,Integer> map) {
		return map.values().stream().mapToInt(i->i).toArray();
	}
	
	public static String[] getSymbolsValence1(HashMap<String,Integer> map, int[] occur) {
		String[] keys= new String[sum(occur)];
		int index=0;
		for(String key: map.keySet()) {
			for(int i=0;i<map.get(key);i++) {
				keys[index]=key;
				index++;
			}
		}
		return keys;
	}
	
	public static List<int[]> rowsGen2(int index) throws CloneNotSupportedException{
		List<int[]> rows= new ArrayList<int[]>();
		int value=Math.min(4, 4-index-1);
		int[] zerosArray= new int[4];
		rows.add(zerosArray);
		for(int v=value;v>0;v--) {
			for(int[] array:part1s(v,v,4-(index+1),0)) {
				int zeros=4-array.length;
				array=addZerosF(array,zeros); //We dont wanna add the zeros; so in the matrix construction, we will add the entries of the previous line.
				rows.add(array);
			}
		}
		return rows;
	}
	
	public static int[] addZerosF(int[] array, int zeros) {
		int[] arr= new int[zeros];
		for(int i=0;i<zeros;i++) {
			arr[i]=0;
		}
		for(int i=0;i<array.length;i++) {
			arr=addElement(arr, array[i]);
		}
		return arr;
	}
	public static List<int[]> part1s(int total,int n, int d,int depth) {
		if(d==depth) {
			List<int[]> array= new ArrayList<int[]>();
			int[] take=new int[0];
			array.add(take);
			return array;
		}
		return buildArr1s(total,n,d,depth);
	}
	
	public static List<int[]> buildArr1s(int total,int n,int d, int depth){
		List<int[]> array= new ArrayList<int[]>();
		IntStream range = IntStream.rangeClosed(0,1);
		for(int i:range.toArray()) {
			for(int[] item: part1s(total,n-i,d,depth+1)) {
				if(item.length==0) {
					if(array.size()==0) {
						item=addElement(item,1);
						array.add(item);
					}else {
						continue;
					}
				}else {
					if(i<2) {
						item=addElement(item,i);
						if(item.length==d) {
							if(sum(item)==total) {
					        	array.add(item);
							}
						}else {
							array.add(item);
						}
					}
				}
			}
		}
		return array;
	}
	
	private void parseArgs(String[] args) throws ParseException
	{
		Options options = setupOptions(args);	
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(options, args);
			GeneratorWithPartGen.molinfo = cmd.getOptionValue("molecularinfo");
			GeneratorWithPartGen.filedir = cmd.getOptionValue("filedir");
			GeneratorWithPartGen.fragments= cmd.getOptionValue("fragments");
			if (cmd.hasOption("verbose")) GeneratorWithPartGen.verbose = true;
		
		} catch (ParseException e) {
			HelpFormatter formatter = new HelpFormatter();
			formatter.setOptionComparator(null);
			String header = "\nGenerates structures for a given molecular information."
					+ " The input is the string of atom symbols with their number of implicit hydrogen."
					+ "For example 'C3C3C3' means three carbon atoms each of which has three implicit hydrogens."
					+ "Besides this molecular information, the directory is needed to be specified for the output"
					+ "file. \n\n";
			String footer = "\nPlease report issues at https://github.com/MehmetAzizYirik/EQGen";
			formatter.printHelp( "java -jar EQGen.jar", header, options, footer, true );
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
		Option fragments = Option.builder("f")
			     .required(false)
			     .hasArg()
			     .longOpt("fragments")
			     .desc("The list of substructures from experimental data")
			     .build();
		options.addOption(fragments);
		return options;
	}
	
	
	public static void main(String[] args) throws CloneNotSupportedException, CDKException, IOException  {		
		IAtomContainer acon= new AtomContainer();
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		/**acon.getAtom(0).setImplicitHydrogenCount(2);
		acon.getAtom(1).setImplicitHydrogenCount(2);
		acon.getAtom(2).setImplicitHydrogenCount(2);
		acon.getAtom(3).setImplicitHydrogenCount(2);
		acon.getAtom(4).setImplicitHydrogenCount(2);
		acon.getAtom(5).setImplicitHydrogenCount(2);**/
		
		acon.addBond(0, 1, Order.SINGLE);
		acon.addBond(1, 2, Order.SINGLE);
		acon.addBond(2, 3, Order.SINGLE);
		acon.addBond(3, 4, Order.SINGLE);
		acon.addBond(4, 5, Order.SINGLE);
		
		PermutationGroup group=getAutomorphismGroup(acon);
		ListMultimap<Integer, Integer> map = ArrayListMultimap.create();
		
		for(int i=0;i<acon.getAtomCount();i++) {
			for(Permutation perm: group.all()) {
				map.put(i, perm.get(i));
			}
		}
		System.out.println(map);
		EquivalentClassPartitioner it = new EquivalentClassPartitioner(acon);
	    int[] equivalentClass = it.getTopoEquivClassbyHuXu(acon);
		System.out.println(Arrays.toString(equivalentClass));
		depict(acon,"C:\\Users\\mehme\\Desktop\\FAUL.png");
		
		/**GeneratorWithPartGen gen = null;
		String[] args1= {"-i","C6H6","-v","-d","C:\\Users\\mehme\\Desktop\\" };
		try {
			gen = new GeneratorWithPartGen();
			gen.parseArgs(args1);
			GeneratorWithPartGen.run(GeneratorWithPartGen.molinfo, GeneratorWithPartGen.filedir);
		} catch (Exception e) {
			if (GeneratorWithPartGen.verbose) e.getCause(); 
		}
		IAtomContainer acon= new AtomContainer();
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addBond(0,1, Order.SINGLE);
		
		int[] array= new int[3];
		array[0]=2;
		array[1]=2;
		array[2]=2;
		
		String[] array2= new String[6];
		array2[0]="Br";
		array2[1]="Br";
		array2[2]="Cl";
		array2[3]="Cl";
		array2[4]="H";
		array2[5]="H";
		
		for(Set<ArrayList<Integer>> set:fundamentalLemma(acon, array, array2)) {
			System.out.println(set.toArray()[0]);
		}
		
		
		IAtomContainer acon= new AtomContainer();
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("C"));
		acon.addAtom(new Atom("O"));
		acon.addAtom(new Atom("O"));
		//acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addAtom(new Atom("H"));
		acon.addBond(0, 14, Order.SINGLE);
		acon.addBond(3, 15, Order.SINGLE);
		acon.addBond(4, 16, Order.SINGLE);
		acon.addBond(5, 17, Order.SINGLE);
		acon.addBond(6, 18, Order.SINGLE);
		acon.addBond(7, 19, Order.SINGLE);
		acon.addBond(8, 20, Order.SINGLE);
		//acon.addBond(9, 21, Order.SINGLE);
		acon.addBond(0, 1, Order.SINGLE);
		acon.addBond(1, 2, Order.DOUBLE);
		acon.addBond(2, 3, Order.SINGLE);
		acon.addBond(3, 4, Order.DOUBLE);
		acon.addBond(4, 5, Order.SINGLE);
		acon.addBond(5, 0, Order.DOUBLE);
		acon.addBond(1, 12, Order.SINGLE);
		acon.addBond(2, 13, Order.SINGLE);
		acon.addBond(12, 10, Order.SINGLE);
		acon.addBond(13, 11, Order.SINGLE);
		acon.addBond(6, 7, Order.DOUBLE);
		acon.addBond(7, 8, Order.SINGLE);
		acon.addBond(8, 9, Order.DOUBLE);
		acon.addBond(9, 10, Order.SINGLE);
		acon.addBond(10, 11, Order.DOUBLE);
		acon.addBond(11, 6, Order.SINGLE);
		
		
		int[] array= new int[3];
		array[0]=3;
		array[1]=2;
		array[2]=2;
		List<int[]> list=truncatedTabloids(array,14);
		for(int[] arr: list) {
			System.out.println(Arrays.toString(arr));
		}
		
		depict(acon,"C:\\Users\\mehme\\Desktop\\after.png");
		AtomContainerDiscretePartitionRefiner refiner = PartitionRefinement.forAtoms().create();
		PermutationGroup autG = refiner.getAutomorphismGroup(acon);
		for(Permutation perm: autG.all()) {
			System.out.println(perm.toCycleString());
			for(int i=0;i<acon.getAtomCount();i++) {
				if(acon.getAtom(i).getSymbol()=="R") {
					System.out.println(i+" "+perm.get(i)+" "+acon.getAtom(perm.get(i)).getSymbol());
				}
			}
		}
		
		AtomContainerDiscretePartitionRefiner refiner = PartitionRefinement.forAtoms().create();
		PermutationGroup autG = refiner.getAutomorphismGroup(acon);
		//PermutationGroup group= refiner.getAutomorphismGroup(acon, PermutationGroup.makeSymN(8));
		
		for(Permutation perm: autG.all()) {
			System.out.println(perm.toCycleString());
			for(int i=0;i<acon.getAtomCount();i++) {
				if(saturationChecker(acon,i)) {
					System.out.println(i+" "+perm.get(i));
				}
			}
		}
		
		GeneratorWithPartGen gen = null;
		String[] args1= {"-i","C3H3","-v","-d","C:\\Users\\mehme\\Desktop\\" };
		try {
			gen = new GeneratorWithPartGen();
			gen.parseArgs(args1);
			GeneratorWithPartGen.run(GeneratorWithPartGen.molinfo, GeneratorWithPartGen.filedir);
		} catch (Exception e) {
			if (GeneratorWithPartGen.verbose) e.getCause(); 
		}
		
		List<int[]> list= new ArrayList<int[]>();
		int[] array= new int[0];
		truncatedTabloids(4,array,list);
		for(int[] a: list) {
			System.out.println(Arrays.toString(a));
		}
		ArrayList<Permutation> R= new ArrayList<Permutation>();
	    Permutation perm1 = new Permutation(3,2,1,0,7,6,5,4);
	    Permutation perm2 = new Permutation(0,1,2,3,4,5,6,7);
	    Permutation perm3 = new Permutation(4,5,6,7,0,1,2,3);
	    Permutation perm4 = new Permutation(7,6,5,4,3,2,1,0);
	    R.add(perm1);
	    R.add(perm2);
	    R.add(perm3);
	    R.add(perm4);
	     
	    PermutationGroup s8= PermutationGroup.makeSymN(8);
	     
	    ArrayList<Permutation> gen= new ArrayList<Permutation>();
	     
	    Permutation gen1= new Permutation(1,2,3,0,4,5,6,7);
	    Permutation gen2= new Permutation(1,0,2,3,4,5,6,7);
	    Permutation gen3= new Permutation(0,1,2,3,5,6,7,4);
	    Permutation gen4= new Permutation(0,1,2,3,5,4,6,7);
	    gen.add(gen1);
	    gen.add(gen2);
	    gen.add(gen3);
	    gen.add(gen4);
	     
	     
	    PermutationGroup s4s4=generateGroup(gen);
	    System.out.println(fundamentalLemma(s8,s4s4,4,R).size());
	    **/

	}
}