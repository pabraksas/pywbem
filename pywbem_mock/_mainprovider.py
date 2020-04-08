#
# (C) Copyright 2018 InovaDevelopment.com
#
# This library is free software; you can redistribute it and/or
# modify it under the terms of the GNU Lesser General Public
# License as published by the Free Software Foundation; either
# version 2.1 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
#
# Author: Karl  Schopmeyer <inovadevelopment.com>
#

"""
Implementation of a CIM general provider that processes:
    The CIMClass request Operations.
    The CIMQualifier request Operations
    The CIMInstance request Enumerate and request pull Operations
    The Associator request operations

This provider uses a separate datastore for the objects maintained by
the repository and defined with the interfaces in _base_repository.py
"""

from __future__ import absolute_import, print_function

from copy import deepcopy
import uuid
from collections import Counter
import six

# pylint: disable=ungrouped-imports
try:
    # time.perf_counter() was added in Python 3.3
    from time import perf_counter as delta_time
except ImportError:
    # time.clock() was deprecated in Python 3.3
    from time import clock as delta_time
# pylint: enable=ungrouped-imports


from pywbem import CIMClass, CIMClassName, \
    CIMInstance, CIMInstanceName, CIMQualifierDeclaration, CIMError, \
    CIM_ERR_NOT_FOUND, CIM_ERR_INVALID_PARAMETER, CIM_ERR_INVALID_CLASS, \
    CIM_ERR_ALREADY_EXISTS, CIM_ERR_INVALID_NAMESPACE, \
    CIM_ERR_INVALID_ENUMERATION_CONTEXT, CIM_ERR_NOT_SUPPORTED, \
    CIM_ERR_QUERY_LANGUAGE_NOT_SUPPORTED, CIM_ERR_NAMESPACE_NOT_EMPTY, \
    CIM_ERR_FAILED
from pywbem._nocasedict import NocaseDict
from pywbem._utils import _format

from ._resolvermixin import ResolverMixin

# Default Max_Object_Count for Fake Server if not specified by request
_DEFAULT_MAX_OBJECT_COUNT = 100

# Maximum Open... timeout if not set by request
OPEN_MAX_TIMEOUT = 40

# Per DSP0200, the default behavior for EnumerateInstance DeepInheritance
# if not set by server.  Default is True.
DEFAULT_DEEP_INHERITANCE = True

# None of the request method names conform since they are camel case
# pylint: disable=invalid-name


class MainProvider(ResolverMixin, object):
    """
    Implementation of a WBEM server CIM repository that implements the
    required WBEM request operations corresponding to the WBEM operations
    defined in DSP0200.

    The MainProvider component of a WBEM server maintains
    a repository of CIMClasses, CIMInstances, and CIMQualifierDeclarations
    which can be manipulated by methods in this class.  This class provides
    the implementation of the methods to manipulate collections of each
    of these object types in seperate namespaces.

    It also includes methods to add namespaces, remove namespaces and
    get a list of the names of current namespaces.

    This CIM repository implementation uses a data store implementation
    defined by the instance constructor (Currently InMemoryRepository) to store
    and retrieve data representing the CIM classes, CIM instances, and
    CIM qualifier declarations.
    """

    def __init__(self, conn, datastore):
        """
        This CIM repository implementation uses a data store implementation
        defined by the constructor (Currently InMemoryRepository) to store
        and retrieve data.

        Parameters:
            conn(:class:`~pywbem_mock.FakeWBEMConnection`):
              The current instance of the connection from which some
              variables are extracted for the repository including
              the host and disable_pull_operations attributes.

            datastore(:class:`~pywbem_mock.InMemoryRepository` or other subclass of `~pywbem_mock.baseRepository`):  # noqa: E501
             class defining the data store for the CIM repository.
        """
        #   Host name required for some responses. this is the host, port
        self.host = conn.host
        self.conn = conn

        # Implementation of the CIM object repository that is the data store
        # for CIM classes, CIM instances, CIM qualifier declarations and
        # CIM methods.  All access to the  CIM data must
        # pass through this variable to the CIM repository.
        # See :py:module:`pywbem_mock/inmemoryrepository` for a description of
        # the repository interface.
        self.datastore = datastore

        # Open Pull Contexts. The key for each context is an enumeration
        # context id.  The data is the total list of instances/names to
        # be returned and the current position in the list. Any context in
        # this list is still open.
        self.enumeration_contexts = {}

    def __repr__(self):
        return _format(
            "MainProvider("
            "datastore={s.datastore}, "
            "host={s.host})",
            s=self)

    @property
    def namespaces(self):
        """
        Return the namespaces that exist in the datastore
        """
        return self.datastore.namespaces

    #####################################################################
    #
    #     Common methods that the MainProvider request processing methods
    #     use to communicate with the defined repository. These are generally
    #     private methods.
    #
    #####################################################################

    def _class_exists(self, namespace, classname):
        """
        Test if class defined by classname parameter exists in
        repository defined by namespace parameter.

        Returns `True` if class exists and `False` if it does not exist.

        Exception if the namespace does not exist
        """
        class_store = self.get_class_store(namespace)
        return class_store.exists(classname)

    @staticmethod
    def _make_tuple(rtn_value):
        """
        Change the return value from the value consistent with the definition
        in cim_operations.py into a tuple in accord with _imethodcall
        """
        return [("IRETURNVALUE", {}, rtn_value)]

    @staticmethod
    def _remove_qualifiers(obj):
        """
        Remove all qualifiers from the input objectwhere the object may
        be an CIMInstance or CIMClass. Removes qualifiers from the object and
        from properties, methods, and parameters

        This is used to process the IncludeQualifier parameter for classes
        and instances
        """
        assert isinstance(obj, (CIMInstance, CIMClass))
        obj.qualifiers = NocaseDict()
        for prop in obj.properties:
            obj.properties[prop].qualifiers = NocaseDict()
        if isinstance(obj, CIMClass):
            for method in obj.methods:
                obj.methods[method].qualifiers = NocaseDict()
                for param in obj.methods[method].parameters:
                    obj.methods[method].parameters[param].qualifiers = \
                        NocaseDict()

    @staticmethod
    def _remove_classorigin(obj):
        """
        Remove all ClassOrigin attributes from the input object. The object
        may be a CIMInstance or CIMClass.

        Used to process the IncludeClassOrigin parameter of requests
        """
        assert isinstance(obj, (CIMInstance, CIMClass))
        for prop in obj.properties:
            obj.properties[prop].class_origin = None
        if isinstance(obj, CIMClass):
            for method in obj.methods:
                obj.methods[method].class_origin = None

    def _get_superclass_names(self, classname, class_store):
        """
        Get list of superclasses names from the class datastore for the
        defined classname (cln) in the namespace.

        Parameters:
          classname(:term:`string` or None):
            Class name for which superclasses will be retrieved.
            If None, an empty list is returned

        Returns:
         List of classnames in order of assending class hierarchy or an
         empty list if classname is None. The list is returned in desending
         hiearchy order.
        """

        superclass_names = []
        if classname is not None:
            cln_work = classname
            while cln_work:
                # Accesses class in repository. Note, no copy made
                cln_superclass = class_store.get(cln_work).superclass
                if cln_superclass:
                    superclass_names.append(cln_superclass)
                cln_work = cln_superclass
            superclass_names.reverse()
        return superclass_names

    def _get_subclass_names(self, classname, class_store, deep_inheritance):
        """
        Get class names that are subclasses of the classname input
        parameter from the datastore.

        If DeepInheritance is False, get only classes in the
        repository for the defined namespace for which this class is a
        direct super class.

        If deep_inheritance is `True`, get all direct and indirect
        subclasses.  If False, get only a the next level of the
        hiearchy.  `None` is treated the same as `False`

        The input classname is NOT included in the returned list.

        Parameters:
          classname (:term:`string` or None):
            The name of the CIM class for which subclass names will
            be retrieved. If None, retrieval starts at the root of
            the class hiearchy

          class_store (:class:`~pywbem_mock.BaseObjectStore):
           The object store to search for this class and subclasses

          deep_inheritance (:class:`py:bool`):

        Returns:
          list of :term:`unicode string` with the names of all subclasses of
          `classname`.

        """

        assert classname is None or isinstance(classname, six.string_types)

        if classname is None:
            rtn_classnames = [
                c.classname for c in class_store.iter_values()
                if c.superclass is None]
        else:
            rtn_classnames = [
                c.classname for c in class_store.iter_values()
                if c.superclass and c.superclass.lower() == classname.lower()]

        # Recurse for next level of class hiearchy
        if deep_inheritance:
            subclass_names = []
            if rtn_classnames:
                for cln in rtn_classnames:
                    subclass_names.extend(
                        self._get_subclass_names(cln, class_store,
                                                 deep_inheritance))
            rtn_classnames.extend(subclass_names)
        return rtn_classnames

    def _get_class(self, namespace, classname, local_only=None,
                   include_qualifiers=None, include_classorigin=None,
                   property_list=None):
        # pylint: disable=invalid-name
        """
        Get class from repository.  Gets the class defined by classname
        from the repository, creates a copy, expands the copied class to
        include superclass properties if not localonly, and filters the
        class based on propertylist and includeClassOrigin.

        It also sets the propagated attribute.

        Parameters:

          classname (:term:`string`):
            Name of class to retrieve

          namespace (:term:`string`):
            Namespace from which to retrieve the class

          local_only (:class:`py:bool`):
            If `True`, only properties and methods in this specific class are
            returned. Otherwise properties and methods from the superclasses
            are included.

          include_qualifiers (:class:`py:bool`):
            If `True`, include qualifiers. Otherwise remove all qualifiers

          include_classorigin (:class:`py:bool`):
            If `True` return the class_origin attributes of properties and
            methods.
            If `False` or `None` (use server default), class_origin attributes
            of properties and methods are not returned

          property_list (list of :term:`string`):
            Properties to be included in returned class.  If None, all
            properties are returned.  If empty list, no properties are returned

        Returns:

          Copy of the CIM class if found with superclass properties
          installed and filtered per the method arguments.

        Raises:
          CIMError: (CIM_ERR_NOT_FOUND) if class Not found in repository or
          CIMError: (CIM_ERR_INVALID_NAMESPACE) if namespace does not exist
        """

        class_store = self.get_class_store(namespace)

        # Try to get the target class and create a copy for response
        try:
            cls = class_store.get(classname)
        except KeyError:
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Class {0!A} not found in namespace {1!A}.",
                        classname, namespace))

        # TODO/ks: changing this to cls.copy() causes failures with
        # class qualifiers not created.
        cc = deepcopy(cls)

        if local_only:
            for prop, pvalue in cc.properties.items():
                if pvalue.propagated:
                    del cc.properties[prop]
            for method, mvalue in cc.methods.items():
                if mvalue.propagated:
                    del cc.methods[method]

        self._filter_properties(cc, property_list)

        if not include_qualifiers:
            self._remove_qualifiers(cc)

        if not include_classorigin:
            self._remove_classorigin(cc)
        return cc

    def _iter_association_classes(self, namespace):
        """
        Return iterator of association classes from the class repo

        Returns the classes that have associations qualifier.
        Does NOT copy so these are what is in repository. User functions
        MUST NOT modify these classes.

        Returns: Returns generator where each yield returns a single
                 association class
        """

        class_store = self.get_class_store(namespace)
        for cl in class_store.iter_values():
            if 'Association' in cl.qualifiers:
                yield cl
        return

    @staticmethod
    def _find_instance(iname, instance_store, copy_inst=None):
        """
        Find an instance in the repository by iname and return
        that instance. the copy_inst controls whether the original
        instance in the object store is returned on only a copy.  The
        only time the original should be returned is when the user is
        certain that the returned object WILL NOT be modified.

        Parameters:

          iname: CIMInstancename to find

          instance_store (:class:`~pywbem_mock.BaseObjectStore):
            The object store to search for the instance

          copy_inst: boolean.
            If True do copy of the instance and return the copy. Otherwise
            return the instance in the repository

        Return (None, None if not found. Otherwise return instance or
        copy of instance

        Raises:

          CIMError: Failed if repo invalid.
        """

        if instance_store.exists(iname):
            if copy_inst:
                return instance_store.get(iname).copy()
            return instance_store.get(iname)

        return None

    def _get_instance(self, namespace, iname, instance_store, property_list,
                      local_only, include_class_origin, include_qualifiers):
        """
        Local method implements the core functionality of a GetInstance
        responder. This is used by other instance methods that need to get an
        instance from the repository.

        It attempts to get the instance, copies it, and filters it
        for input parameters of local_only, include_qualifiers,
        include_class_origin, and propertylist.

        Parameters:

          namespace (:term:`string`)
              Namespace containing the instance. This is used only for
              explanatory data in exceptions

          iname (:class:`~pywbem.CIMInstanceName`)
              The instance name of the instance to be retrieved.


          instance_store (:class:`~pywbem_mock.BaseObjectStore):
            The object store to search for this class and subclasses

          property_list: (:term:`string` or :term:`py:iterable` of :term:`string`)  # noqa: E501
            List of property names that will be used to filter properties
            of the returned instance.  If property_list is None, no
            filtering is done. Otherwise each property name in the
            list defines a property to be retained in the returned instance.
            An empty list causes the method to return an instance with
            no properties.

          local_only:(:class:`pybool`)
              If True only properties with classorigin same as classname
              are returned.

          include_class_origin:(:class:`pybool`)
              If True, class_origin included in returned object.

          include_qualifiers:(:class:`pybool`)
              If True, any qualifiers in the stored instance the instance and
              properties are returned
              NOTE: This is deprecated so generally has no effect.

        Returns:

          CIMInstance copy from the repository with property_list filtered,
          and qualifers removed if include_qualifiers=False and
          class origin removed if include_class_origin False

        Raises:
            CIMError: (CIM_ERR_NOT_FOUND) if the  class instance or required
            superclasses  do not exist in the repository
        """

        rtn_inst = self._find_instance(iname, instance_store, copy_inst=True)

        if rtn_inst is None:
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Instance not found in repository namespace {0!A}. "
                        "Path={1!A}", namespace, iname))

        # If local_only remove properties where class_origin
        # differs from class of target instance
        if local_only:
            for p in rtn_inst:
                class_origin = rtn_inst.properties[p].class_origin
                if class_origin and class_origin != rtn_inst.classname:
                    del rtn_inst[p]

        if local_only:
            # gets class propertylist which may be local only or all
            # superclasses
            try:
                cl = self._get_class(namespace, iname.classname,
                                     local_only=local_only)
            except CIMError as ce:
                if ce.status_code == CIM_ERR_NOT_FOUND:
                    raise CIMError(
                        CIM_ERR_INVALID_CLASS,
                        _format("Class {0!A} not found for instance {1!A} in "
                                "namespace {2!A}.",
                                iname.classname, iname, namespace))

            class_pl = cl.properties.keys()

            for p in list(rtn_inst):
                if p not in class_pl:
                    del rtn_inst[p]

        self._filter_properties(rtn_inst, property_list)

        if not include_qualifiers:
            self._remove_qualifiers(rtn_inst)

        if not include_class_origin:
            self._remove_classorigin(rtn_inst)
        return rtn_inst

    def _get_subclass_list_for_enums(self, classname, namespace, class_store):
        """
        Get class list (i.e names of subclasses for classname for the
        enumerateinstance methods in a case-insenstive dictionary. The input
        classname is included in this dictionary.

        Returns:
           NocaseDict where only the keys are important, This allows case
           insensitive matches of the names with Python "for cln in clns".

        Raises:

            CIMError: (CIM_ERR_INVALID_CLASS) if classname not in repository
        """

        if not class_store.exists(classname):
            raise CIMError(
                CIM_ERR_INVALID_CLASS,
                _format("Class {0!A} not found in namespace {1!A}.",
                        classname, namespace))

        clnslist = self._get_subclass_names(classname, class_store, True)
        clnsdict = NocaseDict()
        for cln in clnslist:
            clnsdict[cln] = cln

        clnsdict[classname] = classname
        return clnsdict

    @staticmethod
    def _filter_properties(obj, property_list):
        """
        Remove properties from an instance or class that aren't in the
        property_list parameter

        obj(:class:`~pywbem.CIMClass` or :class:`~pywbem.CIMInstance):
            The class or instance from which properties are to be filtered

        property_list(list of :term:`string`):
            List of properties which are to be included in the result. If
            None, remove nothing.  If empty list, remove everything. else
            remove properties that are not in property_list. Duplicated names
            are allowed in the list and ignored.
        """
        if property_list is not None:
            property_list = [p.lower() for p in property_list]
            for pname in obj.properties.keys():
                if pname.lower() not in property_list:
                    del obj.properties[pname]

    ###############################################################
    #
    #   Access  to data store
    #
    #   The following methods provide access to the data store for
    #   a single namespace. There are separate methods to provide
    #   access to each of the 3 object stores within the data store
    #   CIMClass, CIMInstance, and CIMQualifierDeclaration.
    #
    ##################################################################

    def get_class_store(self, namespace):
        """
        Returns the class data store for the specified CIM namespace within the
        CIM repository.  This method validates that the namespace exists in the
        CIM repository.

        If the class object store does not contain the namespace an exception
        is generated.

        Parameters:

          namespace(:term:`string`): Namespace name. Must not be `None`.

        Returns:

          Instance of :class:`~pywbem_mock.`BaseObjectStore` which is the
          object store for classes in the repository.

        Raises:

          :exc:`~pywbem.CIMError`: CIM_ERR_INVALID_NAMESPACE: Namespace does
            not exist.
        """
        self.validate_namespace(namespace)
        return self.datastore.get_class_store(namespace)

    def get_instance_store(self, namespace):
        """
        Returns the instance object store for the specified CIM namespace
        within the datastore.  This method validates that the namespace exists.

        If the object store does not contain the namespace an exception
        is generated.

        Parameters:

          namespace(:term:`string`): Namespace name. Must not be `None`.

        Returns:

          :class:`~pywbem_mock.`BaseObjectStore` which is the object store for
           instances in the repository.

        Raises:

          :exc:`~pywbem.CIMError`: CIM_ERR_INVALID_NAMESPACE: Namespace does
            not exist.
        """

        self.validate_namespace(namespace)
        return self.datastore.get_instance_store(namespace)

    def get_qualifier_store(self, namespace):
        """
        Returns the qualifier declaration object store for the specified CIM
        namespace within the datastore.  This method validates that the
        namespace exists.

        If the object store does not contain the namespace an exception
        is generated.

        Parameters:

          namespace(:term:`string`): Namespace name. Must not be `None`.

        Returns:

          :class:`~pywbem_mock.`BaseObjectStore` which is the object store for
           qualifier declarations in the repository.

        Raises:

          :exc:`~pywbem.CIMError`: CIM_ERR_INVALID_NAMESPACE: Namespace does
            not exist.
        """

        self.validate_namespace(namespace)
        return self.datastore.get_qualifier_store(namespace)

    ################################################################
    #
    #   Methods to manage namespaces
    #
    ################################################################

    def validate_namespace(self, namespace):
        """
        Validates that a namespace is defined in the datastore.

          Parameters:

            namespace (:term:`string`):
              The name of the CIM namespace in the datastore. Must not be
              `None`.

          Returns:
             True if the namespace is defined

          Raises:

          :exc:`~pywbem.CIMError`: CIM_ERR_INVALID_NAMESPACE: Namespace does
            not exist.
        """
        try:
            self.datastore.validate_namespace(namespace)
        except KeyError:
            raise CIMError(
                CIM_ERR_INVALID_NAMESPACE,
                _format("Namespace does not exist in datastore: {0!A}",
                        namespace))

    def add_namespace(self, namespace):
        """
        Add a CIM namespace to the datastore.

        The namespace must not yet exist in the datastore.

        Parameters:

          namespace (:term:`string`):
            The name of the CIM namespace in the datastore. Must not be
            `None`. Leading and trailing slash characters are split off
            from the provided string.

        Raises:

          ValueError: Namespace argument must not be None.
          :exc:`~pywbem.CIMError`: CIM_ERR_ALREADY_EXISTS if the namespace
            already exists in the datastore.
        """

        if namespace is None:
            raise ValueError("Namespace argument must not be None")

        try:
            self.datastore.add_namespace(namespace)
        except ValueError:
            raise CIMError(
                CIM_ERR_ALREADY_EXISTS,
                _format("Namespace {0!A} already exists in the datastore ",
                        namespace))

    def remove_namespace(self, namespace):
        """
        Remove a CIM namespace from the datastore.

        The namespace must exist in the datastore and must be empty.

        Parameters:

          namespace (:term:`string`):
            The name of the CIM namespace in the datastore. Must not be
            `None`. Any leading and trailing slash characters are split off
            from the provided string.

        Raises:

          ValueError: Namespace argument must not be None
          :exc:`~pywbem.CIMError`:  CIM_ERR_NOT_FOUND if the namespace does
            not exist in the datastore.
          :exc:`~pywbem.CIMError`:  CIM_ERR_NAMESPACE_NOT_EMPTY if the
            namespace is not empty.
          :exc:`~pywbem.CIMError`:  CIM_ERR_NAMESPACE_NOT_EMPTY if attempting
            to delete the default connection namespace.  This namespace cannot
            be deleted from the datastore
        """
        if namespace is None:
            raise ValueError("Namespace argument must not be None")

        try:
            self.datastore.remove_namespace(namespace)
        except KeyError:
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Namespace {0!A} does not exist in the datastore ",
                        namespace))
        except ValueError:
            raise CIMError(
                CIM_ERR_NAMESPACE_NOT_EMPTY,
                _format("Namespace {0!A} contains objects.", namespace))

    #####################################################################
    #
    #   WBEM server request operation methods. These methods corresponde
    #   directly to the client methods in WBEMConnection.
    #
    #   All the methods are named <methodname> and
    #   are responders that emulate the server response.
    #
    #   The API for these calls differs from the methods in _WBEMConnection
    #   in that every provider call API includes the namespace as a
    #   positional argument including those where _WBEMConnection methods do not
    #   include the namespace. This is logical in that the server
    #   does not have the concept of a default whereas the client does.
    #
    #   The pattern we try to use in the processing is to use the
    #   namespace only to validate namespace, and get the corresponding
    #   repository for the CIM type and namespace from the data store
    #   and use that in further processing. The only other use of namespace
    #   should be in possibly preparing data for sending to the data
    #   store and generating excption messages.
    #
    ######################################################################

    ####################################################################
    #
    #   EnumerateClasses server request
    #
    ####################################################################

    def EnumerateClasses(self, namespace, ClassName=None,
                         DeepInheritance=None, LocalOnly=None,
                         IncludeQualifiers=None, IncludeClassOrigin=None):
        """
        Implements a CIM server responder for
        :meth:`~pywbem.WBEMConnection.EnumerateClasses`.

        Enumerate classes from datastore. If classname parameter
        exists, use it as the starting point for the hiearchy to get subclasses.
        Parameters:

          namespace (:term:`string`):
            Defines the namespace to be used when accessing the datastore
            for this operation. None is not allowed.

          ClassName (:term:`string`):
            Name of the class whose subclasses will be retrieved
            (case independent).

          DeepInheritance (:class:`py:bool`):
            Indicates that all (direct and indirect) subclasses of the
            specified class or of the top-level classes are to be included in
            the result, as follows:

            * If `False`, only direct subclasses of the specified class or only
              top-level classes are included in the result.
            * If `True`, all direct and indirect subclasses of the specified
              class or the top-level classes and all of their direct and
              indirect subclasses are included in the result.
            * If `None`, the server defined default is False
              per :term:`DSP0200` (server-implemented default is `False`).

            Note, the semantics of the `DeepInheritance` parameter in
            :meth:`~pywbem.WBEMConnection.EnumerateInstances` is different.

          LocalOnly (:class:`py:bool`):
            Indicates that inherited properties, methods, and qualifiers are to
            be excluded from the returned classes, as follows.

            * If `False`, inherited elements are not excluded.
            * If `True`, inherited elements are excluded.
            * If `None`, this parameter is not passed to the WBEM server, and
              the server-implemented default `True` to be used per
              :term:`DSP0200`.
            TODO: Confirm that our default is TRUE

          IncludeQualifiers (:class:`py:bool`):
            Indicates that qualifiers are to be included in the returned
            classes, as follows:

            * If `False`, qualifiers are not included.
            * If `True`, qualifiers are included.
            * If `None`, this parameter is not passed to the WBEM server, and
              causes the server-implemented default to be used. :term:`DSP0200`
              defines that the server-implemented default is `True`.
            TODO: Confirm we use True for server defined default

          IncludeClassOrigin (:class:`py:bool`):
            Indicates that class origin information is to be included on each
            property and method in the returned classes, as follows:

            * If `False`, class origin information is not included.
            * If `True`, class origin information is included.
            * If `None`, this the server defined default is False
              per :term:`DSP0200` (server-implemented default is `False`).
            TODO: Confirm we use False

        Returns:

            List of :class:`~pywbem.CIMClass` that are the enumerated classes.

        Raises:

            CIMError: CIM_ERR_INVALID_NAMESPACE: invalid namespace,
            CIMError: CIM_ERR_NOT_FOUND: A class that should be a subclass
            of either the root or "ClassName" parameter was not found in the
            datastore. This is probably a repository build error.
            CIMError: CIM_ERR_INVALID_CLASS: class defined by the classname
            parameter does not exist.
        """

        self.validate_namespace(namespace)
        class_store = self.get_class_store(namespace)

        if ClassName:
            assert(isinstance(ClassName, six.string_types))
            if not class_store.exists(ClassName):
                raise CIMError(
                    CIM_ERR_INVALID_CLASS,
                    _format("The class {0!A} defined by 'ClassName' parameter "
                            "does not exist in namespace {1!A}",
                            ClassName, namespace))

        clns = self._get_subclass_names(ClassName, class_store,
                                        DeepInheritance)

        # Get each class and process it for the modifiers.
        classes = [
            self._get_class(namespace, cln,
                            local_only=LocalOnly,
                            include_qualifiers=IncludeQualifiers,
                            include_classorigin=IncludeClassOrigin)
            for cln in clns]

        return classes

    ####################################################################
    #
    #   EnumerateClasseNames server request
    #
    ####################################################################

    def EnumerateClassNames(self, namespace, ClassName=None,
                            DeepInheritance=None):
        """
        Implements a CIM server responder for
        :meth:`~pywbem.WBEMConnection.EnumerateClassNames`.

        Enumerates the classnames of the classname in the 'classname' parameter
        or from the top of the tree if 'classname is None.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace from which class names are to be retrieved
            (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          ClassName (:term:`string`):
            Name of the class whose subclasses are to be retrieved
            (case independent).

            If `None`, the top-level classes in the namespace will be
            retrieved.

          DeepInheritance (:class:`py:bool`):
            Indicates that all (direct and indirect) subclasses of the
            specified class or of the top-level classes are to be included in
            the result, as follows:

            * If `False`, only direct subclasses of the specified class or only
              top-level classes are included in the result.
            * If `True`, all direct and indirect subclasses of the specified
              class or the top-level classes and all of their direct and
              indirect subclasses are included in the result.
            * If `None`, this parameter is treated as False, as defined in
              :term:`DSP0200` (server-implemented default is `False`).

            Note, the semantics of the `DeepInheritance` parameter in
            :meth:`~pywbem.WBEMConnection.EnumerateInstances` is different.

        Returns:

            A list of :term:`unicode string` objects that are the class names
            of the enumerated classes

        Raises:

            CIMError: CIM_ERR_INVALID_NAMESPACE: invalid namespace,
            CIMError: CIM_ERR_INVALID_CLASS: class defined by the classname
            parameter does not exist
        """

        # Validate namespace and get class_store for this namespace
        self.validate_namespace(namespace)
        class_store = self.get_class_store(namespace)

        if ClassName:
            assert(isinstance(ClassName, six.string_types))
            if not class_store.exists(ClassName):
                raise CIMError(
                    CIM_ERR_INVALID_CLASS,
                    _format("The class {0!A} defined by 'ClassName' parameter "
                            "does not exist in namespace {1!A}",
                            ClassName, namespace))

        # Return list of subclass names
        return self._get_subclass_names(ClassName, class_store, DeepInheritance)

    ####################################################################
    #
    #   GetClass server request
    #
    ####################################################################

    def GetClass(self, namespace, ClassName, LocalOnly=None,
                 IncludeQualifiers=None, IncludeClassOrigin=None,
                 PropertyList=None):
        """
        Implements a  WBEM provider responder  for
        :meth:`~pywbem.WBEMConnection.GetClass

        Retrieve a CIM class from the local repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace from which the class will be retrieved
            (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO

        Returns:
            :class:`~pywbem.CIMClass`

        Raises:
            CIMError: CIM_ERR_INVALID_NAMESPACE: invalid namespace,
            CIMError: CIM_ERR_INVALID_CLASS: class defined by the ClassName
            parameter does not exist in the repository
        """

        self.validate_namespace(namespace)

        assert isinstance(ClassName, six.string_types)

        cc = self._get_class(namespace, ClassName, local_only=LocalOnly,
                             include_qualifiers=IncludeQualifiers,
                             include_classorigin=IncludeClassOrigin,
                             property_list=PropertyList)

        return cc

    ####################################################################
    #
    #   CreateClass server request
    #
    ####################################################################

    def CreateClass(self, namespace, NewClass, ):
        """
        Implements a  WBEM request responder for
        :meth:`~pywbem.WBEMConnection.CreateClass`

        Creates a new class in the repository.  Nothing is returned.

        TODO: The following is not correct
        If the class repository for this namespace does not
        exist, this method creates it.

        Classes that are in the repository contain only the properties in
        the new_class, not any properties from inheritated classes.  The
        corresponding _get_class resolves any inherited properties to create
        a complete class with both local and inherited properties.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the class defined by NewClass will
            be retrieved (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO

        Raises:
            CIMError: CIM_ERR_INVALID_SUPERCLASS if superclass specified bu
              does not exist.

            CIMError: CIM_ERR_INVALID_PARAMETER if NewClass parameter not a
              class.

            CIMError: CIM_ERR_ALREADY_EXISTS if class already exists.
        """
        self.validate_namespace(namespace)
        # Validate parameters
        if not isinstance(NewClass, CIMClass):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("NewClass not valid CIMClass. Rcvd type={0}",
                        type(NewClass)))

        # Validate namespace in class store and get the class datastore
        # for this namespace.
        class_store = self.get_class_store(namespace)

        if class_store.exists(NewClass.classname):
            raise CIMError(
                CIM_ERR_ALREADY_EXISTS,
                _format("Class {0!A} already exists in namespace {1!A}.",
                        NewClass.classname, namespace))

        new_class = NewClass.copy()

        qualifier_store = self.get_qualifier_store(namespace)
        self._resolve_class(new_class, namespace, qualifier_store,
                            verbose=False)

        # Add new class to repository
        class_store.create(new_class.classname, new_class)

    ####################################################################
    #
    #   ModifyClass server request
    #
    ####################################################################

    def ModifyClass(self, namespace, ModifiedClass):
        # pylint: disable=unused-argument
        """
        Currently not implemented
        Implements a  CIM repository server responder for
        :meth:`~pywbem.WBEMConnection.MmodifyClass`

        Modifies a class in the datastore.  Nothing is returned.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace containing the class that will be modified
            (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO

        Raises:

            CIMError: CIM_ERR_NOT_SUPPORTED
        """

        self.validate_namespace(namespace)

        raise CIMError(
            CIM_ERR_NOT_SUPPORTED,
            "Currently ModifyClass not supported in Fake_WBEMConnection")

    ####################################################################
    #
    #   DeleteClass server request
    #
    ####################################################################

    def DeleteClass(self, namespace, ClassName):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.DeleteClass`

        Delete a class in the class repository if it exists.

        This method also deletes any subclasses and CIM instances of
        the target class or its subclasses.

        Nothing is returned.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace containing the class defined by ClassName that
            will be deleted (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO

        Raises:

            CIMError: CIM_ERR_NOT_FOUND if ClassName defines class not in
                repository
        """

        # Validate namespace and get the class datastore for this namespace
        class_store = self.get_class_store(namespace)
        instance_store = self.get_instance_store(namespace)

        if not class_store.exists(ClassName):
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Class {0!A} in namespace {1!A} not in repository. "
                        "Nothing deleted.", ClassName, namespace))

        # create list of subclass names and append the target class
        classnames = self._get_subclass_names(ClassName, class_store, True)
        classnames.append(ClassName)

        # Delete all instances in this class and subclasses and delete
        # this class and subclasses
        for clname in classnames:
            sub_clns = self._get_subclass_list_for_enums(ClassName, namespace,
                                                         class_store)

            inst_paths = [inst.path for inst in instance_store.iter_values()
                          if inst.path.classname in sub_clns]

            for ipath in inst_paths:
                instance_store.delete(ipath)

            class_store.delete(clname)

    ##########################################################
    #
    #              Faked Qualifier methods
    #
    ###########################################################

    ####################################################################
    #
    #   EnumerateQualifiers server request
    #
    ####################################################################

    def EnumerateQualifiers(self, namespace):
        # pylint: disable=unused-argument
        """
        Imlements a  WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.EnumerateQualifiers`

        Enumerates the qualifier declarations in the local datastore of
        namespace.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace containind the qualifier declarations to be
            returned (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

        Returns:
          A list of :class:`~pywbem.CIMQualifierDeclaration` objects that are
          representations of the enumerated qualifier declarations.

        Raises:
          CIMError: CIM_ERROR_INVALID_NAMESPACE
        """

        # Validate namespace and get qualifier_store for this namespace
        qualifier_store = self.get_qualifier_store(namespace)

        # pylint: disable=unnecessary-comprehension
        qualifiers = [q for q in qualifier_store.iter_values()]

        return qualifiers

    ####################################################################
    #
    #   GetGetQualifier server request
    #
    ####################################################################

    def GetQualifier(self, namespace, QualifierName):
        """
        Implements a WBEM provider responder for
        :meth:`pywbem.WBEMConnection.GetQualifier`.

        Retrieves a qualifier declaration from the local repository of this
        namespace.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace from which the qualifier declaration
            QualifierName will be retrieved (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          QualifierName (:term:`string`):
            Name of the qualifier declaration to be retrieved
            (case independent).

        Returns:

          A :class:`~pywbem.CIMQualifierDeclaration` object that is a
            representation of the retrieved qualifier declaration.

        Raises:
            CIMError: CIM_ERR_INVALID_NAMESPACE
            CIMError: CIM_ERR_NOT_FOUND
        """

        # Validate namespace and get qualifier_store for this namespace
        qualifier_store = self.get_qualifier_store(namespace)

        try:
            qualifier = qualifier_store.get(QualifierName)
        except KeyError:
            ce = CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Qualifier declaration {0!A} not found in namespace "
                        "{1!A}.", QualifierName, namespace))
            raise ce

        return qualifier

    ####################################################################
    #
    #   SetQualifier server request
    #
    ####################################################################

    def SetQualifier(self, namespace, QualifierDeclaration):
        """
        Implements a WBEM provider responder for
        :meth:`pywbem.WBEMConnection.SetQualifier`.

        Create or modify a qualifier declaration in the local repository of this
        class.  This method will create a new namespace for the qualifier
        if none is defined.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in in which the QualifierDeclaration will be
            created or modified (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          QualifierDeclaration (:class:`~pywbem.CIMQualifierDeclaration`):
            Representation of the qualifier declaration to be created or
            modified.

        Raises:

            CIMError: CIM_ERR_INVALID_PARAMETER
            CIMError: CIM_ERR_ALREADY_EXISTS
        """

        # Validate namespace and get the qualifier data store for this namespace
        qualifier_store = self.get_qualifier_store(namespace)

        qual_decl = QualifierDeclaration
        if not isinstance(qual_decl, CIMQualifierDeclaration):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("QualifierDeclaration parameter is not a valid "
                        "valid CIMQualifierDeclaration. Rcvd type={0}, "
                        "Object={1}", type(qual_decl), qual_decl))

        # Try to create and if that fails, modify the existing qualifier decl
        try:
            qualifier_store.create(qual_decl.name, qual_decl)
        except ValueError:
            try:
                qualifier_store.update(qual_decl.name, qual_decl)
            except KeyError:
                raise CIMError(
                    CIM_ERR_FAILED,
                    _format("Qualifier declaration {0!A} could not be "
                            "created or modified in namespace {1!A}.",
                            qual_decl.name, namespace))

    ####################################################################
    #
    #   DeleteQualifier server request
    #
    ####################################################################

    def DeleteQualifier(self, namespace, QualifierName):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.DeleteQualifier`

        Deletes a single qualifier if it is in the
        repository for this class and namespace

        Parameters:

          namespace (:term:`string`):
            Name of the namespace from which the qualifier declaration named
            QualifierName will be deleted (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          QualifierName (:term:`string`):
            Name of the qualifier declaration to be deleted (case independent).

        Raises;

            CIMError: CIM_ERR_INVALID_NAMESPACE,
            CIMError: CIM_ERR_NOT_FOUND
        """

        # Validate namespace and get the qualifier data store for this namespace
        qualifier_store = self.get_qualifier_store(namespace)

        if qualifier_store.exists(QualifierName):
            qualifier_store.delete(QualifierName)
        else:
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("QualifierDeclaration {0!A} not found in namespace "
                        "{1!A}.", QualifierName, namespace))

    #####################################################################
    #
    #  CIM Instance server request responder methods
    #
    #####################################################################

    ####################################################################
    #
    #   CreateInstance server request
    #
    ####################################################################

    def CreateInstance(self, namespace, NewInstance):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.CreateInstance`

        Create a CIM instance in the local repository of this class.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
            (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          NewInstance (:class:`~pywbem.CIMInstance`):
            A representation of the CIM instance to be created.

            The `classname` attribute of this object specifies the creation
            class for the new instance.

            The namespace of the `path` attribute must be `None` or the
            same as the namespace parameter.

            The `properties` attribute of this object specifies initial
            property values for the new CIM instance.

            Instance-level qualifiers have been deprecated in CIM, so any
            qualifier values specified using the `qualifiers` attribute
            of this object are ignored.

        Returns:
            CIMInstanceName with the server defined instance path
            for the new instance.

        Raises:

            CIMError: CIM_ERR_ALREADY_EXISTS
              The instance defined by namespace and instance name already
              exists.

            CIMError: CIM_ERR_INVALID_CLASS
              The class defined in NewInstance  does not exist in the
              namespace.
        """

        new_instance = NewInstance
        if not isinstance(new_instance, CIMInstance):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("NewInstance parameter is not a valid CIMInstance. "
                        "Rcvd type={0}", type(new_instance)))

        # Validate namespace
        instance_store = self.get_instance_store(namespace)

        # Requires corresponding class to build path to be returned
        try:
            target_class = self._get_class(namespace,
                                           new_instance.classname,
                                           local_only=False,
                                           include_qualifiers=True,
                                           include_classorigin=True)
        except CIMError as ce:
            if ce.status_code != CIM_ERR_NOT_FOUND:
                raise

            raise CIMError(
                CIM_ERR_INVALID_CLASS,
                _format("Cannot create instance because its creation "
                        "class {0!A} does not exist in namespace {1!A}.",
                        new_instance.classname, namespace))

        # Handle namespace creation, currently hard coded.
        # Issue #2062 TODO/AM 8/18 Generalize the hard coded handling into
        # provider concept
        classname_lower = new_instance.classname.lower()
        if classname_lower == 'pg_namespace':
            ns_classname = 'PG_Namespace'
        elif classname_lower == 'cim_namespace':
            ns_classname = 'CIM_Namespace'
        else:
            ns_classname = None
        if ns_classname:
            try:
                new_namespace = new_instance['Name']
            except KeyError:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Namespace creation via CreateInstance: "
                            "Missing 'Name' property in the {0!A} instance ",
                            new_instance.classname))

            # Normalize the namespace name
            # TODO: We should not have to normalize here, that is lower level
            new_namespace = new_namespace.strip('/')

            # Write it back to the instance in case it was changed
            new_instance['Name'] = new_namespace

            # These values must match those in
            # tests/unittest/utils/wbemserver_mock.py.
            new_instance['CreationClassName'] = ns_classname
            new_instance['ObjectManagerName'] = 'MyFakeObjectManager'
            new_instance['ObjectManagerCreationClassName'] = \
                'CIM_ObjectManager'
            new_instance['SystemName'] = 'Mock_Test_WBEMServerTest'
            new_instance['SystemCreationClassName'] = 'CIM_ComputerSystem'

        # Test all key properties in instance. The CIM repository
        # cannot add values for key properties and does
        # not allow creating key properties from class defaults.
        key_props = [p.name for p in six.itervalues(target_class.properties)
                     if 'key' in p.qualifiers]
        for pn in key_props:
            if pn not in new_instance:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Key property {0!A} not in NewInstance ", pn))

        # Exception if property in instance but not class or types do not
        # match
        for iprop_name in new_instance:
            if iprop_name not in target_class.properties:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Property {0!A} specified in NewInstance is not "
                            "exposed by class {1!A} in namespace {2!A}",
                            iprop_name, target_class.classname, namespace))

            cprop = target_class.properties[iprop_name]
            iprop = new_instance.properties[iprop_name]
            if iprop.is_array != cprop.is_array or \
                    iprop.type != cprop.type:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Instance and class property {0!A} types "
                            "do not match: instance={1!A}, class={2!A}",
                            iprop_name, iprop, cprop))

            # The class and instnames are the same except for possible case
            # sensitivity. If case different, set cprop_name into new instance
            # to maintain case equality
            cprop_name = cprop.name
            if cprop_name != iprop_name:
                new_instance.properties[iprop_name].name = cprop_name

        # If property not in instance, add it from class and use default value
        # from class
        for cprop_name in target_class.properties:
            if cprop_name not in new_instance:
                default_value = target_class.properties[cprop_name]
                new_instance[cprop_name] = default_value

        # Build instance path. We build the complete instance path
        new_instance.path = CIMInstanceName.from_instance(
            target_class,
            new_instance,
            namespace=namespace)

        # Check for duplicate instances
        if instance_store.exists(new_instance.path):
            raise CIMError(
                CIM_ERR_ALREADY_EXISTS,
                _format("NewInstance {0!A} already exists in namespace "
                        "{1!A}.", new_instance.path, namespace))

        # Reflect the new namespace in the  CIM repository
        # TODO: This should not be necessary with data store
        if ns_classname:
            self.add_namespace(new_namespace)

        # Store the new instance in the  CIM repository
        instance_store.create(new_instance.path, new_instance)

        # Create instance returns model path, path relative to namespace
        # TODO: Change to use copy

        return new_instance.path.copy()

    ####################################################################
    #
    #   ModifyInstance server request
    #
    ####################################################################

    def ModifyInstance(self, namespace, ModifiedInstance,
                       IncludeQualifiers=None, PropertyList=None):
        # pylint: disable=unused-argument
        # pylint: disable=invalid-name,line-too-long
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.CreateInstance`

        Modify a CIM instance in the local repository.

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
            (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          ModifiedInstance (:class:`~pywbem.CIMInstance`):
            A representation of the modified instance, also indicating its
            instance path.

            The `path` attribute of this object identifies the instance to be
            modified. Its `keybindings` attribute is required. If its
            `namespace` attribute is not `None`, it must be the namespace
            defined by the namespace argument.
            Its `host` attribute will be ignored.

            The `classname` attribute of the instance path and the `classname`
            attribute of the instance must specify the same class name.

            The properties defined in this object specify the new property
            values (including `None` for NULL). If a property is designated to
            be modified but is not specified in this object, the WBEM server
            will use the default value of the property declaration if specified
            (including `None`), and otherwise may update the property to any
            value (including `None`).

          IncludeQualifiers (:class:`py:bool`):
            Indicates that qualifiers are to be modified as specified in the
            `ModifiedInstance` parameter, as follows:

            * If `False`, qualifiers not modified.
            * If `True`, qualifiers are modified if the WBEM server implements
              support for this parameter.
            * If `None`, this parameter is not passed to the WBEM server, and
              causes the server-implemented default to be used. :term:`DSP0200`
              defines that the server-implemented default is `True`.

            This parameter has been deprecated in :term:`DSP0200`. Clients
            cannot rely on qualifiers to be modified.  This implementation
            ignores this parameter.

          PropertyList (:term:`string` or :term:`py:iterable` of :term:`string`):
            This parameter defines which properties are designated to be
            modified.

            This parameter is an iterable specifying the names of the
            properties, or a string that specifies a single property name. In
            all cases, the property names are matched case insensitively.
            The specified properties are designated to be modified. Properties
            not specified are not designated to be modified.

            An empty iterable indicates that no properties are designated to be
            modified.

            If `None`, DSP0200 states that the properties with values different
            from the current values in the instance are designated to be
            modified, but for all practical purposes this is equivalent to
            stating that all properties exposed by the instance are designated
            to be modified.

        Raises:

            CIMError: CIM_ERR_ALREADY_EXISTS,
            CIMError: CIM_ERR_INVALID_CLASS
            CIMError: CIM_ERR_INVALID_PARAMETER
            CIMError: CIM_ERR_NAMESPACE_NOT_FOUND
        """  # noqa: E501
        # pylint: disable=invalid-name,line-too-long

        # TODO: validate namespace variations
        # Validate namespace and get instance data store
        instance_store = self.get_instance_store(namespace)
        modified_instance = ModifiedInstance.copy()
        property_list = PropertyList

        # Return if empty property list, nothing would be changed
        if property_list is not None and not property_list:
            return

        if not isinstance(modified_instance, CIMInstance):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("The ModifiedInstance parameter is not a valid "
                        "CIMInstance. Rcvd type={0}", type(modified_instance)))

        # Classnames in instance and path must match
        if modified_instance.classname.lower() != \
                modified_instance.path.classname.lower():
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("ModifyInstance classname in path and instance do "
                        "not match. classname={0!A}, path.classname={1!A}",
                        modified_instance.classname,
                        modified_instance.path.classname))

        # Get class including properties from superclasses from  CIM repository
        # NOTE: TODO This call differs from client call in that:
        #    1. The namespace is not an argument
        try:
            target_class = self._get_class(
                namespace,
                modified_instance.classname,
                local_only=False,
                include_qualifiers=True,
                include_classorigin=True,
                property_list=None)
        except CIMError as ce:
            if ce.status_code == CIM_ERR_NOT_FOUND:
                raise CIMError(
                    CIM_ERR_INVALID_CLASS,
                    _format("Cannot modify instance because its creation "
                            "class {0!A} does not exist in namespace {1!A}.",
                            modified_instance.classname, namespace))
            raise

        # Get original instance in datastore.
        if modified_instance.path.namespace is None:
            modified_instance.path.namespace = namespace

        orig_instance = self._find_instance(modified_instance.path,
                                            instance_store,
                                            copy_inst=True)
        if orig_instance is None:
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Original Instance {0!A} not found in namespace {1!A}",
                        modified_instance.path, namespace))

        # Remove duplicate properties from property_list
        if property_list:
            if len(property_list) != len(set(property_list)):
                property_list = list(set(property_list))

        # Test that all properties in modified instance and property list
        # are in the class
        if property_list:
            for p in property_list:
                if p not in target_class.properties:
                    raise CIMError(
                        CIM_ERR_INVALID_PARAMETER,
                        _format("Property {0!A} in PropertyList not in class "
                                "{1!A}", p, modified_instance.classname))
        for p in modified_instance:
            if p not in target_class.properties:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Property {0!A} in ModifiedInstance not in class "
                            "{1!A}", p, modified_instance.classname))

        # Set the class value for properties in the property list but not
        # in the modified_instance. This sets just the value component.
        mod_inst_props = set([k.lower() for k in modified_instance.keys()])
        cl_props = [pn.lower() for pn in target_class.properties]
        chngd_props = mod_inst_props.difference(set(cl_props))
        if chngd_props:
            for prop in chngd_props:
                modified_instance[prop] = \
                    target_class.properties[prop].value

        # Remove all properties that do not change value between original
        # instance and modified instance
        for p in list(modified_instance):
            if orig_instance[p] == modified_instance[p]:
                del modified_instance[p]

        # Confirm no key properties in remaining modified instance
        key_props = [p.name for p in six.itervalues(target_class.properties)
                     if 'key' in p.qualifiers]
        for p in key_props:
            if p in modified_instance:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("ModifyInstance cannot modify key property {0!A}",
                            p))

        # Remove any properties from modified instance not in the property_list
        if property_list:
            for p in list(modified_instance):  # create list before loop
                if p not in property_list:
                    del modified_instance[p]

        # Exception if property in instance but not class or types do not
        # match
        for pname in modified_instance:
            if pname not in target_class.properties:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Property {0!A} specified in ModifiedInstance is "
                            "not exposed by class {1!A} in namespace {2!A}",
                            pname, target_class.classname, namespace))

            cprop = target_class.properties[pname]
            iprop = modified_instance.properties[pname]
            if iprop.is_array != cprop.is_array \
                    or iprop.type != cprop.type \
                    or iprop.array_size != cprop.array_size:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("Instance and class property name={0!A} type "
                            "or other attributes do not match: "
                            "instance={1!A}, class={2!A}",
                            pname, iprop, cprop))
            # If case of modified_instance property != case of class property
            # change the name in the modified_instance
            if iprop.name != cprop.name:
                modified_instance.properties[iprop.name].name = cprop.name

        # Modify the value of properties in the repo with those from
        # modified instance inserted into the original instance
        orig_instance.update(modified_instance.properties)
        instance_store.update(modified_instance.path, orig_instance)

        return

    ####################################################################
    #
    #   GetInstance server request
    #
    ####################################################################

    def GetInstance(self, namespace, InstanceName, LocalOnly=None,
                    IncludeQualifiers=None, IncludeClassOrigin=None,
                    PropertyList=None):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.GetInstance`.

        Gets a single instance from the repository based on the
        InstanceName and filters it for PropertyList, etc.

        This method uses a common repository access method _get_instance to
        get, copy, and process the instance.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Raises:

            CIMError:  CIM_ERR_INVALID_NAMESPACE, CIM_ERR_INVALID_PARAMETER
              CIM_ERR_NOT_FOUND
        """

        if InstanceName.namespace is None:
            iname = InstanceName.copy()
            iname.namespace = namespace
        else:
            iname = InstanceName

        if iname.namespace != namespace:
            raise CIMError(
                CIM_ERR_INVALID_NAMESPACE,
                _format("GetInstance Namespace {0!A} in InstanceName {1!A} "
                        "does not match provided namespace.", iname.namespace,
                        iname, namespace))

        instance_store = self.get_instance_store(namespace)

        if not self._class_exists(namespace, iname.classname):
            raise CIMError(
                CIM_ERR_INVALID_CLASS,
                _format("Class {0!A} for GetInstance of instance {1!A} "
                        "does not exist.", iname.classname, iname))

        inst = self._get_instance(namespace, iname, instance_store,
                                  PropertyList,
                                  LocalOnly,
                                  IncludeClassOrigin,
                                  IncludeQualifiers)

        return inst

    ####################################################################
    #
    #   DeleteInstance server request
    #
    ####################################################################

    def DeleteInstance(self, namespace, InstanceName):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.DeleteInstance`.

        This deletes a single instance from the CIM repository based on the
        namespace and InstanceNameparameters.

        It does not attempt to delete referencing instances (associations,
        etc.) that reference this instance.

        TODO: This moves to the provider.
        If the creation class of the instance to be deleted is PG_Namespace or
        CIM_Namespace, then the namespace identified by the 'Name' property
        of the instance is being deleted in the CIM repository in addition to
        the CIM instance. The default connection namespace of this faked
        commection cannot be deleted.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          InstanceName (:class:`~pywbem.CIMInstanceName`):
            The instance path of the instance to be deleted.
            If this object specifies a namespace, it must be the same as the
            namespace argument.
            Its `host` attribute will be ignored.


        """
        if InstanceName.namespace is None:
            iname = InstanceName.copy()
            iname.namespace = namespace
        else:
            iname = InstanceName

        if iname.namespace != namespace:
            raise CIMError(
                CIM_ERR_INVALID_NAMESPACE,
                _format("DeleteInstance Namespace {0!A} in InstanceName {1!A} "
                        "does not match provided namespace.", iname.namespace,
                        iname, namespace))

        # Validate namespace and get instance datastore
        instance_store = self.get_instance_store(namespace)

        if not self._class_exists(namespace, iname.classname):
            raise CIMError(
                CIM_ERR_INVALID_CLASS,
                _format("Class {0!A} in namespace {1!A} not found. "
                        "Cannot delete instance {2!A}",
                        iname.classname, namespace, iname))

        if not instance_store.exists(iname):
            raise CIMError(
                CIM_ERR_NOT_FOUND,
                _format("Instance {0!A} not found in repository namespace "
                        "{1!A}", iname, namespace))

        # Handle namespace deletion, currently hard coded.
        # Issue #2062 TODO/AM 8/18 Generalize the hard coded handling into
        # provider concept
        classname_lower = iname.classname.lower()
        if classname_lower == 'pg_namespace':
            ns_classname = 'PG_Namespace'
        elif classname_lower == 'cim_namespace':
            ns_classname = 'CIM_Namespace'
        else:
            ns_classname = None
        if ns_classname:
            namespace = iname.keybindings['Name']

            # Reflect the namespace deletion in the CIM repository
            # This will check the namespace for being empty.
            self.remove_namespace(namespace)

        # Delete the instance from the repository
        instance_store.delete(iname)

    ####################################################################
    #
    #   EnumerateInstances server request
    #
    ####################################################################

    def EnumerateInstances(self, namespace, ClassName, LocalOnly=None,
                           DeepInheritance=None, IncludeQualifiers=None,
                           IncludeClassOrigin=None, PropertyList=None):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.EnumerateInstances`.

        Gets a list of subclasses if the classes exist in the repository
        then executes getInstance for each to create the list of instances
        to be returned.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Raises:

            CIMError: CIM_ERR_INVALID_NAMESPACE
        """

        # Validate namespace
        instance_store = self.get_instance_store(namespace)
        class_store = self.get_class_store(namespace)

        assert isinstance(ClassName, six.string_types)

        # If DeepInheritance False use only properties from the original
        # class. Modify property list to limit properties to those from this
        # class.  This only works if class exists. If class not in
        # repository, ignore DeepInheritance.

        # If None, set to server default
        if DeepInheritance is None:
            DeepInheritance = DEFAULT_DEEP_INHERITANCE

        pl = PropertyList
        lo = LocalOnly

        # gets class propertylist which may be localonly or all
        # superclasses
        cl = self._get_class(namespace, ClassName, local_only=lo)
        class_pl = cl.properties.keys()

        # If not di, compute property list to filter
        # all instances to the properties in the target class as modified
        # by the PropertyList
        if not DeepInheritance:
            if pl is None:  # properties in class form property list
                pl = class_pl
            else:      # reduce pl to properties in class_properties
                pl_lower = [pc.lower() for pc in pl]
                pl = [pc for pc in class_pl if pc.lower() in pl_lower]

        clns_dict = self._get_subclass_list_for_enums(ClassName, namespace,
                                                      class_store)

        insts = [self._get_instance(namespace, inst.path, instance_store,
                                    pl,
                                    None,  # LocalOnly never gets passed
                                    IncludeClassOrigin, IncludeQualifiers)
                 for inst in instance_store.iter_values()
                 if inst.path.classname in clns_dict]

        return insts

    ####################################################################
    #
    #   EnumerateInstanceNames server request
    #
    ####################################################################

    def EnumerateInstanceNames(self, namespace, ClassName):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.EnumerateInstanceNames`

        Get instance names for instances that match the path defined
        by `ClassName` and return a list of the names.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO

        """

        assert isinstance(ClassName, six.string_types)

        # Validate namespace and get instance datastore for this namespace
        instance_store = self.get_instance_store(namespace)
        class_store = self.get_class_store(namespace)

        clns = self._get_subclass_list_for_enums(ClassName, namespace,
                                                 class_store)

        inst_paths = [inst.path for inst in instance_store.iter_values()
                      if inst.path.classname in clns]

        return_paths = [path.copy() for path in inst_paths]

        return return_paths

    ####################################################################
    #
    #   ExecQuery server request
    #
    ####################################################################

    def ExecQuery(self, namespace, QueryLanguage, Query):
        # pylint: disable=unused-argument
        """
        Implements a WBEM provider responder for
            :meth:`~pywbem.WBEMConnection.ExecQuery`

        Executes the the query defined by the QueryLanguage and Query parameter
        in the namespace defined.

        NOTE: This operation currently returns CIM_ERR_NOT_SUPPORTED

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """

        self.validate_namespace(namespace)

        raise CIMError(
            CIM_ERR_NOT_SUPPORTED,
            "ExecQuery not implemented!")

    #####################################################################
    #
    #  Faked WBEMConnection Reference and Associator methods
    #
    #####################################################################

    def _return_assoc_class_tuples(self, rtn_classnames, namespace, iq, ico,
                                   pl):
        """
        Creates the correct tuples of for associator and references class
        level responses from a list of classnames.  This is special because
        the class level references and associators return a tuple of
        CIMClassName and CIMClass for every entry.
        """

        rtn_tups = []
        for cn in rtn_classnames:
            rtn_tups.append((CIMClassName(cn, namespace=namespace,
                                          host=self.host),
                             self._get_class(namespace, cn,
                                             include_qualifiers=iq,
                                             include_classorigin=ico,
                                             property_list=pl)))
        return rtn_tups

    def _subclasses_lc(self, classname, class_store):
        """
        Return a list of this class and it subclasses in lower case.
        Exception if class is not in repository.
        """
        if not classname:
            return []
        clns = [classname]
        clns.extend(self._get_subclass_names(classname, class_store, True))
        return [cln.lower() for cln in clns]

    def _validate_class_exists(self, namespace, cln, req_param="TargetClass"):
        """
        Common test for the References and Associators requests to test for the
        existence of the class named cln in namespace.

        Returns if the class exists.

        If the class does not exist, executes an INVALID_PARAMETER
        exception which is the specified exception for invalid classes for
        the TargetClass, AssocClass, and ResultClass for reference and
        associator operations
        """
        if not self._class_exists(namespace, cln):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format('Class {0!A} {1} parameter not found in namespace '
                        '{2!A}.', cln, req_param, namespace))

    @staticmethod
    def _ref_prop_matches(prop, target_classnames, ref_classname,
                          resultclass_names, role):
        """
        Test filters for a reference property
        Returns `True` if matches the criteria.

        Returns `False` if it does not match.

        The match criteria are:
          - target_classnames includes prop_reference_class
          - if result_classes are not None, ref_classname is in result_classes
          - If role is not None, prop name matches role
        """

        assert prop.type == 'reference'
        if prop.reference_class.lower() in target_classnames:
            if resultclass_names and ref_classname not in resultclass_names:
                return False
            if role and prop.name.lower() != role:
                return False
            return True
        return False

    @staticmethod
    def _assoc_prop_matches(prop, ref_classname,
                            assoc_classes, result_classes, result_role):
        """
        Test filters of a reference property and its associated entity
        Returns `True` if matches the criteria. Returns `False` if it does not
        match.

        Matches if ref_classname in assoc_classes, and result_role matches
        property name  and reference_class
        """

        assert prop.type == 'reference'
        if assoc_classes and ref_classname.lower() not in assoc_classes:
            return False
        if result_classes and  \
                prop.reference_class.lower() not in result_classes:
            return False
        if result_role and prop.name.lower() != result_role:
            return False
        return True

    def _get_reference_classnames(self, namespace, classname, class_store,
                                  result_class, role):
        """
        Get list of classnames that are references for which this classname
        is a target filtered by the result_class and role parameters if they
        are none.
        This is a common method used by all of the other reference and
        associator methods to create a list of reference classnames

        Returns:
            list of classnames that satisfy the criteria.
        """
        class_store = self.get_class_store(namespace)
        self._validate_class_exists(namespace, classname, "TargetClass")

        if result_class:
            self._validate_class_exists(namespace, result_class, "ResultClass")

        # get list of subclasses in lower case.
        result_classes = self._subclasses_lc(result_class, class_store)

        # Get the set of superclasses for the target classname and set
        # lower case
        target_classlist = self._get_superclass_names(classname, class_store)
        target_classlist.append(classname)
        target_classlist = [cn.lower() for cn in target_classlist]

        # add results to set to avoid any duplicates
        rtn_classnames_set = set()
        # set role to lowercase if it exists
        role = role.lower() if role else role

        # Iterate through class repo getting association classes for namespace
        for assoc_cl in self._iter_association_classes(namespace):
            for prop in six.itervalues(assoc_cl.properties):
                if prop.type == 'reference' and \
                        self._ref_prop_matches(prop, target_classlist,
                                               assoc_cl.classname.lower(),
                                               result_classes,
                                               role):
                    rtn_classnames_set.add(assoc_cl.classname)

        return list(rtn_classnames_set)

    def _get_reference_instnames(self, instname, namespace, class_store,
                                 result_class, role):
        """
        Get the reference instances from the repository for the target
        instname and filtered by the result_class and role parameters.

        Returns a list of the reference instance names. The returned list is
        the original, not a copy so the user must copy them
        """

        instance_store = self.get_instance_store(namespace)

        if not class_store.exists(instname.classname):
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                _format("Class {0!A} not found in namespace {1!A}.",
                        instname.classname, namespace))

        # Get list of class and subclasses in lower case
        if result_class:
            self._validate_class_exists(namespace, result_class, "ResultClass")
        resultclasses = self._subclasses_lc(result_class, class_store)

        instname.namespace = namespace
        role = role.lower() if role else None

        # Future TODO/ks: Search very wide here.  Not isolating to associations
        # and not limiting to expected result_classes. Consider making list from
        # get_reference_classnames if classes exist, otherwise set list to
        # instance_store to search all instances

        rtn_instpaths = set()
        for inst in instance_store.iter_values():
            for prop in six.itervalues(inst.properties):
                if prop.type == 'reference':
                    # Does this prop instance name match target inst name
                    if prop.value == instname:
                        if result_class:
                            if inst.classname.lower() not in resultclasses:
                                continue
                        if role and prop.name.lower() != role:
                            continue
                        rtn_instpaths.add(inst.path)

        return rtn_instpaths

    def _get_associated_classnames(self, namespace, classname, assoc_class,
                                   result_class, result_role, role):
        """
        Get list of classnames that are associated classes for which this
        classname is a target filtered by the assoc_class, role, result_class,
        and result_role parameters if they are none.

        This is a common method used by all of the other reference and
        associator methods to create a list of reference classnames

        Returns:
            list of classnames that satisfy the criteria.
        """

        # Validate namespace and get class_store for this namespace
        class_store = self.get_class_store(namespace)
        if assoc_class:
            self._validate_class_exists(namespace, assoc_class, "AssocClass")

        if result_class:
            self._validate_class_exists(namespace, result_class, "ResultClass")

        # Get list of subclasses for result and assoc classes (lower case)
        result_classes = self._subclasses_lc(result_class, class_store)
        assoc_classes = self._subclasses_lc(assoc_class, class_store)

        rtn_classnames_set = set()

        role = role.lower() if role else role
        result_role = result_role.lower() if result_role else result_role

        ref_clns = self._get_reference_classnames(namespace, classname,
                                                  class_store, assoc_class,
                                                  role)

        # Find reference properties that have multiple use of
        # same reference_class
        klasses = [class_store.get(cln) for cln in ref_clns]
        for cl in klasses:
            # Count reference property usage.
            pd = Counter([p.reference_class for p in
                          six.itervalues(cl.properties)
                          if p.type == 'reference'])
            single_use = [p for p, v in pd.items() if v == 1]

            for prop in six.itervalues(cl.properties):
                if prop.type == 'reference':
                    if self._assoc_prop_matches(prop,
                                                cl.classname,
                                                assoc_classes,
                                                result_classes,
                                                result_role):
                        # Test of referemce cln same as source class
                        if prop.reference_class == classname and \
                                prop.reference_class in single_use:
                            continue

                        rtn_classnames_set.add(prop.reference_class)

        return list(rtn_classnames_set)

    def _get_associated_instancenames(self, namespace, inst_name, assoc_class,
                                      result_class, result_role, role):
        """
        Get the reference instances from the repository for the target
        instname and filtered by the result_class and role parameters.

        Returns a list of the reference instance names. The returned list is
        the original, not a copy so the user must copy them
        """

        instance_store = self.get_instance_store(namespace)
        class_store = self.get_class_store(namespace)

        if assoc_class:
            self._validate_class_exists(namespace, assoc_class, "AssocClass")

        if result_class:
            self._validate_class_exists(namespace, result_class, "ResultClass")

        result_classes = self._subclasses_lc(result_class, class_store)
        assoc_classes = self._subclasses_lc(assoc_class, class_store)

        inst_name.namespace = namespace
        role = role.lower() if role else role
        result_role = result_role.lower() if result_role else result_role

        ref_paths = self._get_reference_instnames(inst_name, namespace,
                                                  class_store,
                                                  assoc_class, role)

        # Get associated instance names
        rtn_instpaths = set()
        for ref_path in ref_paths:
            inst = self._find_instance(ref_path, instance_store)
            for prop in six.itervalues(inst.properties):
                if prop.type == 'reference':
                    if prop.value == inst_name:
                        if assoc_class \
                                and inst.classname.lower() not in assoc_classes:
                            continue
                        if role and prop.name.lower() != role:
                            continue
                    else:
                        if result_class and (prop.value.classname.lower()
                                             not in result_classes):
                            continue
                        if result_role and prop.name.lower() != result_role:
                            continue
                        rtn_instpaths.add(prop.value)
        return rtn_instpaths

    ####################################################################
    #
    #   ReferenceNames server request
    #
    ####################################################################

    def ReferenceNames(self, namespace, ObjectName, ResultClass=None,
                       Role=None):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.ReferenceNames`

        Retrieve the instance paths of the association instances that reference
        a source instance, or the class paths of the association classes that
        reference a source class from the CIM instances in the datastore.  The
        association instances defining the relationship between ObjectName and
        result classes must exist in the datastore.

        This method performs the ReferenceNames operation
        (see :term:`DSP0200`). See :ref:`WBEM operations` for a list of all
        methods performing such operations.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """

        self.validate_namespace(namespace)
        class_store = self.get_class_store(namespace)

        role = Role
        obj_name = ObjectName

        if isinstance(obj_name, CIMInstanceName):
            ref_paths = self._get_reference_instnames(obj_name, namespace,
                                                      class_store,
                                                      ResultClass,
                                                      role)
            rtn_names = [r.copy() for r in ref_paths]

            for iname in rtn_names:
                if iname.host is None:
                    iname.host = self.host

            return rtn_names

        ref_classnames = self._get_reference_classnames(namespace,
                                                        obj_name,
                                                        class_store,
                                                        ResultClass,
                                                        role)

        ref_result = [CIMClassName(classname=cn, host=self.host,
                                   namespace=namespace)
                      for cn in ref_classnames]

        return ref_result

    ####################################################################
    #
    #   References server request
    #
    ####################################################################

    def References(self, namespace, ObjectName, ResultClass=None, Role=None,
                   IncludeQualifiers=None, IncludeClassOrigin=None,
                   PropertyList=None):
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.References`

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """

        # validate namespace and get class_storesitory for this namespace
        class_store = self.get_class_store(namespace)

        role = Role
        obj_name = ObjectName

        if isinstance(obj_name, CIMInstanceName):
            # This is an  instance reference
            instance_store = self.get_instance_store(namespace)
            assert isinstance(obj_name, CIMInstanceName)
            ref_paths = self._get_reference_instnames(obj_name, namespace,
                                                      class_store, ResultClass,
                                                      role)

            rtn_insts = [self._get_instance(namespace, path, instance_store,
                                            None,
                                            PropertyList, IncludeClassOrigin,
                                            IncludeQualifiers)
                         for path in ref_paths]

            for inst in rtn_insts:
                if inst.path.host is None:
                    inst.path.host = self.host

            return rtn_insts

        rtn_classnames = self._get_reference_classnames(
            namespace, obj_name, class_store, ResultClass, role)
        # returns list of tuples of (CIMClassname, CIMClass)
        return self._return_assoc_class_tuples(rtn_classnames, namespace,
                                               PropertyList, IncludeClassOrigin,
                                               IncludeQualifiers)

    ####################################################################
    #
    #   AssociatorNames server request
    #
    ####################################################################

    def AssociatorNames(self, namespace, ObjectName, AssocClass=None,
                        ResultClass=None, Role=None, ResultRole=None):
        # pylint: disable=invalid-name
        """
        Implements a WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.AssociatorNames`

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """

        self.validate_namespace(namespace)

        role = Role
        result_role = ResultRole
        obj_name = ObjectName

        if isinstance(obj_name, CIMInstanceName):
            rtn_paths = self._get_associated_instancenames(namespace,
                                                           obj_name,
                                                           AssocClass,
                                                           ResultClass,
                                                           result_role, role)
            results = [p.copy() for p in rtn_paths]

            for iname in results:
                if iname.host is None:
                    iname.host = self.host

        else:
            rtn_classnames = self._get_associated_classnames(namespace,
                                                             obj_name,
                                                             AssocClass,
                                                             ResultClass,
                                                             result_role, role)
            # TODO: Returns CIMClassName. Should be just the classname
            results = [CIMClassName(classname=cln, host=self.host,
                                    namespace=namespace)
                       for cln in rtn_classnames]

        return results

    ####################################################################

    #   Associators server request
    #
    ####################################################################

    def Associators(self, namespace, ObjectName, AssocClass=None,
                    ResultClass=None,
                    Role=None, ResultRole=None, IncludeQualifiers=None,
                    IncludeClassOrigin=None, PropertyList=None):
        """
        Implements a mock WBEM provider responder for
            :meth:`~pywbem.WBEMConnection.Associators`

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """

        self.validate_namespace(namespace)

        role = Role
        result_role = ResultRole
        obj_name = ObjectName

        if isinstance(obj_name, CIMInstanceName):
            assoc_names = self._get_associated_instancenames(namespace,
                                                             obj_name,
                                                             AssocClass,
                                                             ResultClass,
                                                             result_role, role)
            results = []
            instance_store = self.get_instance_store(namespace)
            for obj_name in assoc_names:
                results.append(self._get_instance(
                    namespace, obj_name, instance_store, None,
                    PropertyList, IncludeClassOrigin, IncludeQualifiers))

            return results

        # Processing obj_name is class name
        rtn_classnames = self._get_associated_classnames(namespace,
                                                         obj_name,
                                                         AssocClass,
                                                         ResultClass,
                                                         result_role, role)
        # returns list of tuples of (CIMClassname, CIMClass)
        return self._return_assoc_class_tuples(rtn_classnames, namespace,
                                               PropertyList, IncludeClassOrigin,
                                               IncludeQualifiers)

    #####################################################################
    #
    #  Faked WBEMConnection Open and Pull Instances Methods
    #
    #  All of the following methods take the simplistic approach of getting
    #  all of the data from the original functions and saving it
    #  in the contexts dictionary.
    #
    #####################################################################

    @staticmethod
    def _create_contextid():
        """Return a new uuid for an enumeration context"""
        return str(uuid.uuid4())

    def _open_response(self, namespace, objects, pull_type, OperationTimeout,
                       MaxObjectCount, ContinueOnError):
        """
        Build response to any Open... request once the objects have been
        extracted from the repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        max_obj_cnt = MaxObjectCount
        if max_obj_cnt is None:
            max_obj_cnt = _DEFAULT_MAX_OBJECT_COUNT

        if ContinueOnError is None:
            ContinueOnError = False

        default_server_timeout = 40
        timeout = default_server_timeout if OperationTimeout is None \
            else OperationTimeout

        # If objects returne in open lt max_obj_cnt, set Enum context to
        # complete status.
        if len(objects) <= max_obj_cnt:
            eos = u'TRUE'
            context_id = ""
            rtn_objects = objects
        # Otherwise create an entry in the open context
        # table, return incomplete status.
        else:
            eos = u'FALSE'
            context_id = self._create_contextid()
            # Issue #2063  Use the timeout along with response delay.
            # Then user could timeout pulls. This means adding timer test to
            # pulls and close. Timer should be used to close old contexts.
            # Also The 'time' item contains elapsed time in fractional seconds
            # since an undefined point in time, so it is only useful for
            # calculating deltas.
            self.enumeration_contexts[context_id] = \
                {'pull_type': pull_type,
                 'data': objects,
                 'namespace': namespace,
                 'time': delta_time(),
                 'interoptimeout': timeout,
                 'continueonerror': ContinueOnError}
            rtn_objects = objects[0:max_obj_cnt]
            # remove objects from list that are being sent to client
            del objects[0: max_obj_cnt]

        return(rtn_objects, eos, context_id)

    def _pull_response(self, req_type, EnumerationContext,
                       MaxObjectCount):
        """
        Common method for all of the Pull methods. Since all of the pull
        methods operate independent of the type of data, this single function
        severs as common code

        This method validates the EnumerationContext, gets data on the
        enumeration sequence from the enumeration_contexts table, validates the
        pull type, and returns the required number of objects.

        This method assumes the same context_id throughout the sequence.

        Returns: Tuple of CIM objects, EndOfSequence flag, EnumerationContext

        Raises:

            CIMError: CIM_ERR_INVALID_ENUMERATION_CONTEXT
        """

        try:
            context_data = self.enumeration_contexts[EnumerationContext]
        except KeyError:
            raise CIMError(
                CIM_ERR_INVALID_ENUMERATION_CONTEXT,
                _format("EnumerationContext {0!A} not found in CIM repository "
                        "enumeration contexts.", EnumerationContext))

        self.validate_namespace(context_data['namespace'])

        if context_data['pull_type'] != req_type:
            raise CIMError(
                CIM_ERR_INVALID_ENUMERATION_CONTEXT,
                _format("Invalid pull operations {0!A} does not match "
                        "expected {1!A} for EnumerationContext {2!A}",
                        context_data['pull_type'], req_type,
                        EnumerationContext))

        objs_list = context_data['data']

        max_obj_cnt = MaxObjectCount
        if not max_obj_cnt:
            max_obj_cnt = _DEFAULT_MAX_OBJECT_COUNT

        if len(objs_list) <= max_obj_cnt:
            eos = u'TRUE'
            rtn_objs_list = objs_list
            del self.enumeration_contexts[EnumerationContext]
            context_id = ""
        else:
            eos = u'FALSE'
            rtn_objs_list = objs_list[0: max_obj_cnt]
            del objs_list[0: max_obj_cnt]

        # returns tuple of list of insts, eos, and context_id
        return (rtn_objs_list, eos, context_id)

    @staticmethod
    def _validate_open_params(FilterQueryLanguage, FilterQuery,
                              OperationTimeout):
        """
        Validate the fql parameters and if invalid, generate exception
        """
        if not FilterQueryLanguage and FilterQuery:
            raise CIMError(
                CIM_ERR_INVALID_PARAMETER,
                "FilterQuery without FilterQueryLanguage definition is "
                "invalid")
        if FilterQueryLanguage:
            if FilterQueryLanguage != 'DMTF:FQL':
                raise CIMError(
                    CIM_ERR_QUERY_LANGUAGE_NOT_SUPPORTED,
                    _format("FilterQueryLanguage {0!A} not supported",
                            FilterQueryLanguage))
        ot = OperationTimeout
        if ot:
            if not isinstance(ot, six.integer_types) or ot < 0 \
                    or ot > OPEN_MAX_TIMEOUT:
                raise CIMError(
                    CIM_ERR_INVALID_PARAMETER,
                    _format("OperationTimeout {0!A }must be positive integer "
                            "less than {1!A}", ot, OPEN_MAX_TIMEOUT))

    def _pull_operations_disabled(self):
        """
        Test if pull operations valid.  If they are not, raise exception
        """
        if self.conn.disable_pull_operations:
            raise CIMError(CIM_ERR_NOT_SUPPORTED,
                           "Pull Operations not supported. "
                           "disable_pull_operations=True")

    ####################################################################
    #
    #   The pull operations
    #   The following implement the server side of the WBEM pull
    #   operations including the Open...(), Pull...(), and Close()
    #
    ####################################################################

    ####################################################################
    #
    #   OpenEnumerateInstancePaths server request
    #
    ####################################################################

    def OpenEnumerateInstancePaths(self, namespace, ClassName,
                                   FilterQueryLanguage=None, FilterQuery=None,
                                   OperationTimeout=None, ContinueOnError=None,
                                   MaxObjectCount=None):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenEnumerationInstancePaths`
        with data from the instance repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        result = self.EnumerateInstanceNames(namespace, ClassName)

        return self._open_response(namespace, result,
                                   'PullInstancePaths',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenEnumerateInstances server request
    #
    ####################################################################

    def OpenEnumerateInstances(self, namespace, ClassName,
                               DeepInheritance=None,
                               IncludeClassOrigin=None, PropertyList=None,
                               FilterQueryLanguage=None, FilterQuery=None,
                               OperationTimeout=None, ContinueOnError=None,
                               MaxObjectCount=None):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenEnumerationInstances`
        with data from the instance repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        result = self.EnumerateInstances(
            namespace, ClassName,
            DeepInheritance=DeepInheritance,
            IncludeQualifiers=None,              # not used with this request
            IncludeClassOrigin=IncludeClassOrigin,
            PropertyList=PropertyList)

        return self._open_response(namespace, result,
                                   'PullInstancesWithPath',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenReferenceInstancePaths server request
    #
    ####################################################################

    def OpenReferenceInstancePaths(self, namespace, InstanceName,
                                   ResultClass=None, Role=None,
                                   FilterQueryLanguage=None, FilterQuery=None,
                                   OperationTimeout=None, ContinueOnError=None,
                                   MaxObjectCount=None):
        # pylint: disable=invalid-name
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenReferenceInstancePaths`
        with data from the instance repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        instances = self.ReferenceNames(namespace, InstanceName,
                                        ResultClass=ResultClass,
                                        Role=Role)

        return self._open_response(namespace, instances,
                                   'PullInstancePaths',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenReferenceInstances server request
    #
    ####################################################################

    def OpenReferenceInstances(self, namespace, InstanceName,
                               ResultClass=None, Role=None,
                               IncludeClassOrigin=None, PropertyList=None,
                               FilterQueryLanguage=None, FilterQuery=None,
                               OperationTimeout=None, ContinueOnError=None,
                               MaxObjectCount=None):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenReferenceInstances`
        with data from the instance repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        # TODO: NOW validate ContinueOnError
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        instances = self.References(namespace, InstanceName,
                                    ResultClass=ResultClass,
                                    Role=Role,
                                    IncludeClassOrigin=IncludeClassOrigin,
                                    PropertyList=PropertyList)

        return self._open_response(namespace, instances,
                                   'PullInstancesWithPath',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenAssociatorInstancePaths server request
    #
    ####################################################################

    def OpenAssociatorInstancePaths(self, namespace, InstanceName,
                                    AssocClass=None, ResultClass=None,
                                    Role=None, ResultRole=None,
                                    FilterQueryLanguage=None, FilterQuery=None,
                                    OperationTimeout=None, ContinueOnError=None,
                                    MaxObjectCount=None):
        # pylint: disable=invalid-name
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenAssociatorInstancePaths`
        with data from the instance repository.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        instances = self.AssociatorNames(namespace, InstanceName,
                                         AssocClass=AssocClass,
                                         ResultClass=ResultClass, Role=Role,
                                         ResultRole=ResultRole)

        return self._open_response(namespace, instances,
                                   'PullInstancePaths',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenAssociatorInstances server request
    #
    ####################################################################

    def OpenAssociatorInstances(self, namespace, InstanceName, AssocClass=None,
                                ResultClass=None, Role=None, ResultRole=None,
                                IncludeClassOrigin=None,
                                PropertyList=None, FilterQueryLanguage=None,
                                FilterQuery=None, OperationTimeout=None,
                                ContinueOnError=None, MaxObjectCount=None):
        """
        Implements WBEM provider responder for
        WBEMConnection.OpenAssociatorInstances
        with data from the instance store.

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        instances = self.Associators(namespace, InstanceName,
                                     AssocClass=AssocClass,
                                     ResultClass=ResultClass, Role=Role,
                                     ResultRole=ResultRole,
                                     IncludeClassOrigin=IncludeClassOrigin,
                                     PropertyList=PropertyList)

        return self._open_response(namespace, instances,
                                   'PullInstancesWithPath',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   OpenQueryInstances server request
    #
    ####################################################################

    def OpenQueryInstances(self, namespace, FilterQueryLanguage, FilterQuery,
                           ReturnQueryResultClass=None,
                           OperationTimeout=None, ContinueOnError=None,
                           MaxObjectCount=None):
        # pylint: disable=invalid-name
        # pylint: disable=unused-argument
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenQueryInstances`
        with data from the instance repository.

        NOTE: Since ExecQuery is not implemented this method also returns
        the not implemented exception

        Parameters:

          namespace (:term:`string`):
            Name of the namespace in which the CIM instance will be created
              (case independent).

            Leading and trailing slash characters will be stripped. The lexical
            case will be preserved.

          TODO: Add remaining parameter definitions

        Returns: TODO

        Raises: CIM_ERR_NOT_IMPLEMENTED
        """
        self._pull_operations_disabled()
        self.validate_namespace(namespace)
        self._validate_open_params(FilterQueryLanguage, FilterQuery,
                                   OperationTimeout)

        # pylint: disable=assignment-from-no-return
        # Issue #2064 TODO/ks implement execquery
        # Handle ReturnQueryResultClass maybe or make it exception
        instances = self.ExecQuery(namespace, FilterQueryLanguage, FilterQuery)

        return self._open_response(namespace, instances,
                                   'PullInstancesWithPath',
                                   OperationTimeout,
                                   MaxObjectCount,
                                   ContinueOnError)

    ####################################################################
    #
    #   PullInstancesWithPath server request
    #
    ####################################################################

    def PullInstancesWithPath(self, EnumerationContext, MaxObjectCount):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenPullInstancesWithPath`
        with data from the instance repository.

        Parameters:

          EnumerationContext(:term:`String`):
            Identifier for the enumeration context created by the
            corresponding Open... request.

          MaxObjectCount(:term:`Integer`):
            Positive integer that defines the maximum number of instances
            that may be returned from this request.

        Returns:
          List of CIMInstances TODO

        Raises:
            CIMError: TODO
        """
        self._pull_operations_disabled()
        return self._pull_response('PullInstancesWithPath',
                                   EnumerationContext, MaxObjectCount)

    ####################################################################
    #
    #   PullInstancePaths server request
    #
    ####################################################################

    def PullInstancePaths(self, EnumerationContext, MaxObjectCount):
        """
        Implements CIM repository responder for
        :meth:`~pywbem.WBEMConnection.OpenPullInstancePaths`
        with data from the instance repository.

        Parameters:
          EnumerationContext(:term:`String`):
            Identifier for the enumeration context created by the
            corresponding Open... request.

          MaxObjectCount(:term:`Integer`):
            Positive integer that defines the maximum number of instances
            that may be returned from this request.

        Returns:
          List of CIMInstances TODO

        Raises:
            CIMError:
        """
        self._pull_operations_disabled()
        return self._pull_response('PullInstancePaths',
                                   EnumerationContext, MaxObjectCount)

    ####################################################################
    #
    #   PullInstances server request
    #
    ####################################################################

    def PullInstances(self, EnumerationContext, MaxObjectCount):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.OpenPullInstances`
        with data from the instance repository.

        Parameters:

          EnumerationContext(:term:`String`):
            Identifier for the enumeration context created by the
            corresponding Open... request.

          MaxObjectCount(:term:`Integer`):
            Positive integer that defines the maximum number of instances
            that may be returned from this request.

        Returns:
          List of CIMInstances TODO

        Raises:
            CIMError:
        """
        self._pull_operations_disabled()
        return self._pull_response('PullInstances',
                                   EnumerationContext, MaxObjectCount)

    ####################################################################
    #
    #   CloseEnumeration server request
    #
    ####################################################################

    def CloseEnumeration(self, EnumerationContext):
        """
        Implements WBEM provider responder for
        :meth:`~pywbem.WBEMConnection.CloseEnumeration`
        with data from the instance repository.

        If the EnumerationContext is valid and open it removes it from the
        context repository. Otherwise it returns an exception.

        Parameters:

          EnumerationContext(:term:`String`):
            Identifier for the enumeration context created by the
            corresponding Open... request.

        Returns: TODO

        Raises: TODO
        """
        self._pull_operations_disabled()

        if EnumerationContext in self.enumeration_contexts:
            del self.enumeration_contexts[EnumerationContext]
        else:
            raise CIMError(
                CIM_ERR_INVALID_ENUMERATION_CONTEXT,
                _format("EnumerationContext {0!A} not found in CIM server "
                        "enumeration contexts.", EnumerationContext))
