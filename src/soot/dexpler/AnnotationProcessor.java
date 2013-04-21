/* Soot - a Java Optimization Framework
 * Copyright (C) 2012 Michael Markert, Frank Hartmann
 * 
 * (c) 2012 University of Luxembourg - Interdisciplinary Centre for
 * Security Reliability and Trust (SnT) - All rights reserved
 * Alexandre Bartel
 * 
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package soot.dexpler;

import org.jf.dexlib.AnnotationItem;
import org.jf.dexlib.AnnotationDirectoryItem;
import org.jf.dexlib.AnnotationSetItem;
import org.jf.dexlib.MethodIdItem;
import org.jf.dexlib.TypeIdItem;
import org.jf.dexlib.ClassDefItem;
import org.jf.dexlib.EncodedValue.AnnotationEncodedSubValue;
import org.jf.dexlib.EncodedValue.EncodedValue;
import org.jf.dexlib.EncodedValue.IntEncodedValue;
import org.jf.dexlib.EncodedValue.StringEncodedValue;
import org.jf.dexlib.EncodedValue.TypeEncodedValue;
import org.jf.dexlib.EncodedValue.MethodEncodedValue;
import org.jf.dexlib.EncodedValue.ArrayEncodedValue;

import soot.SootClass;
import soot.tagkit.EnclosingMethodTag;
import soot.tagkit.InnerClassTag;
import soot.tagkit.Tag;

class AnnotationProcessor
{
	static void process(DexClass c, SootClass sc, DexlibWrapper wrapper)
	{
		Debug.printDbg("+--+ ", sc.getName());
		AnnotationDirectoryItem annotDirItem = c.getAnnotations();
		if(annotDirItem == null)
			return;
		AnnotationSetItem annotSetItem = annotDirItem.getClassAnnotations();
		if(annotSetItem == null)
			return;

		String enclosingClassName = null;
		String className = null;
		int modifier = -1;
		boolean nested = false;
		EnclosingMethodTag encloseMethTag = null;

		for (AnnotationItem annotItem : annotSetItem.getAnnotations()) {
			AnnotationEncodedSubValue val = annotItem.getEncodedAnnotation();
			String type = val.annotationType.getTypeDescriptor();
			if(type.equals("Ldalvik/annotation/InnerClass;")){
				//this is a inner class
				nested = true;
				assert val.names.length == 2;
				for (int i=0; i < val.names.length; i++) {
					String name = val.names[i].getStringValue();
					EncodedValue encodedValue = val.values[i];
					String v;
					if(name.equals("accessFlags"))
						modifier = ((IntEncodedValue)encodedValue).value;
					else if(name.equals("name")){
						switch (encodedValue.getValueType()) {
						case VALUE_NULL:
							className = "null"; //anonymous class
							break;
						case VALUE_STRING:
							className = ((StringEncodedValue)encodedValue).value.getStringValue();
							break;
						default:
							throw new RuntimeException("unexpected "+encodedValue);
						}
					}
					else
						throw new RuntimeException("unexpected "+name);
				}
				Debug.printDbg("InnerClass ", className, " ", modifier);
			}
			else if(type.equals("Ldalvik/annotation/EnclosingClass;")){
				//this class is defined inside a class
				assert val.names.length == 1;
				String name = val.names[0].getStringValue();
				EncodedValue encodedValue = val.values[0];
				if(name.equals("value")){
					switch (encodedValue.getValueType()) {
					case VALUE_TYPE:
						enclosingClassName = ((TypeEncodedValue)encodedValue).value.getTypeDescriptor();
						enclosingClassName = enclosingClassName.substring(1, enclosingClassName.length()-1);
						break;
					default:
						throw new RuntimeException("unexpected "+encodedValue);
					}
				}
				else
					throw new RuntimeException("unexpected "+name);
				Debug.printDbg("EnclosingClass ", enclosingClassName);
			}
			else if(type.equals("Ldalvik/annotation/EnclosingMethod;")){
				//this class is defined inside a method
				assert val.names.length == 1;
				String name = val.names[0].getStringValue();
				EncodedValue encodedValue = val.values[0];
				String v = null;
				if(name.equals("value")){
					switch (encodedValue.getValueType()) {
					case VALUE_METHOD:
						MethodIdItem methIdItem = ((MethodEncodedValue)encodedValue).value;
						String methName = methIdItem.getMethodName().getStringValue();
						String declClassName = methIdItem.getContainingClass().getTypeDescriptor();
						declClassName = declClassName.substring(1, declClassName.length()-1);
						String methSig = methIdItem.getPrototype().getPrototypeString();
						
						v = declClassName + " "+methName+" "+methSig;
						encloseMethTag = new EnclosingMethodTag(declClassName, methName, methSig);
						break;
					default:
						throw new RuntimeException("unexpected "+encodedValue);
					}
				}
				else
					throw new RuntimeException("unexpected "+name);
				Debug.printDbg("EnclosingMethod ", v);
			}
			else if(type.equals("Ldalvik/annotation/MemberClasses;")){
				//this class is the enclosing class for one or more inner class
				assert val.names.length == 1;
				String name = val.names[0].getStringValue();
				EncodedValue encodedValue = val.values[0];
				if(name.equals("value")){
					switch (encodedValue.getValueType()) {
					case VALUE_ARRAY:
						for(EncodedValue eval : ((ArrayEncodedValue)encodedValue).values){
							TypeIdItem typeIdItem = ((TypeEncodedValue) eval).value;
							String innerSig = typeIdItem.getTypeDescriptor();
							innerSig = innerSig.substring(1, innerSig.length()-1);
							String outerSig = c.getType().getTypeDescriptor();
							outerSig = outerSig.substring(1, outerSig.length()-1);

							int innerModifier = getModifierOfInnerClass(wrapper.getDexClasses().get(Util.dottedClassName(typeIdItem.getTypeDescriptor())));
							String innerName = innerSig.substring(innerSig.lastIndexOf('$')+1);
							sc.addTag(new InnerClassTag(innerSig, outerSig, innerName, innerModifier));
						}
						break;
					default:
						throw new RuntimeException("unexpected "+encodedValue);
					}
				}
				else
					throw new RuntimeException("unexpected "+name);
				Debug.printDbg("MemberClass ", encodedValue);				
			}
			else
				Debug.printDbg("unhandled annotation ", type);
		}
		
		if(nested){
			assert modifier >= 0;
			String innerSig = c.getType().getTypeDescriptor();
			innerSig = innerSig.substring(1, innerSig.length()-1);
			sc.addTag(new InnerClassTag(innerSig, enclosingClassName, className, modifier));
		} 
		if(encloseMethTag != null){
			assert enclosingClassName == null;
			sc.addTag(encloseMethTag);
		}
	} 
	
	private static int getModifierOfInnerClass(ClassDefItem cDefItem)
	{
		AnnotationSetItem annotSetItem = cDefItem.getAnnotations().getClassAnnotations();

		int modifier = -1;
		for (AnnotationItem annotItem : annotSetItem.getAnnotations()) {
			AnnotationEncodedSubValue val = annotItem.getEncodedAnnotation();
			String type = val.annotationType.getTypeDescriptor();
			if(type.equals("Ldalvik/annotation/InnerClass;")){
				assert val.names.length == 2;
				assert modifier < 0;
				for (int i=0; i < val.names.length; i++) {
					String name = val.names[i].getStringValue();
					EncodedValue encodedValue = val.values[i];
					if(name.equals("accessFlags"))
						modifier = ((IntEncodedValue)encodedValue).value;
				}
			}
		}
		assert modifier >= 0;
		return modifier;
	}
}