//go:build windows

// File/Directory diff tool with HTML output
// Copyright (C) 2012   Siu Pin Chao
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
package main

import (
	"os"
	"reflect"
	"sync"
	"syscall"
	"unsafe"
)

const has_mmap = true

var winMapperMutex sync.Mutex
var winMapperHandle = make(map[uintptr]syscall.Handle)

// Implement mmap for windows
func map_file(file *os.File, offset, size int) ([]byte, error) {

	// create the mapping handle
	h, err := syscall.CreateFileMapping(syscall.Handle(file.Fd()), nil, syscall.PAGE_READONLY, 0, uint32(size), nil)
	if err != nil {
		return nil, err
	}

	// perform the file map operation
	addr, err := syscall.MapViewOfFile(h, syscall.FILE_MAP_READ, uint32(offset>>32), uint32(offset), uintptr(size))
	if err != nil {
		return nil, err
	}

	// store the mapping handle
	winMapperMutex.Lock()
	winMapperHandle[addr] = h
	winMapperMutex.Unlock()

	// Slice memory layout
	sl := reflect.SliceHeader{Data: addr, Len: size, Cap: size}

	// Use unsafe to turn sl into a []byte.
	bp := *(*[]byte)(unsafe.Pointer(&sl))

	return bp, err
}

// Implement unmap_file for windows
func unmap_file(data []byte) error {

	// Use unsafe to get the buffer address
	addr := uintptr(unsafe.Pointer(&data[0]))

	// retrieve the mapping handle
	winMapperMutex.Lock()
	h := winMapperHandle[addr]
	delete(winMapperHandle, addr)
	winMapperMutex.Unlock()

	// unmap file view
	err := syscall.UnmapViewOfFile(addr)

	// close the mapping handle
	if err == nil {
		err = syscall.CloseHandle(h)
	}

	return err
}
