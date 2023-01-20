/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

package gov.nasa.jpf.symbc.numeric.solvers;
/**
 * 
 */

/**
 * @author Sokharith Sok
 *
 */
public class Yices {
  public native void hello_world();
  public native void yicesl_set_verbosity(short l);
  public native String yicesl_version();
  public native void yicesl_enable_type_checker(short flag);
  public native void yicesl_enable_log_file(String filename);
  public native int yicesl_mk_context();
  public native void yicesl_del_context(int ctx);
  public native int yicesl_read(int ctx, String cmd);
  public native int yicesl_inconsistent(int ctx);
  public native String yicesl_get_last_error_message();
  public native void yicesl_set_output_file(String filename);
  static{
    String yicesLibraryPath = System.getProperty("yices.library.path");
    System.load(yicesLibraryPath);
  }
}
